--[[ Core/DirtySystem.lua
     Simplified dirty flag system for player data updates.

     For 32-100 player servers, we don't need complex bitmask queues.
     A simple hash table with per-player dirty reason sets is:
     - O(1) lookups
     - No bitwise operations
     - No queue synchronization
     - Cleaner code

     Usage:
       DirtySystem.MarkDirty(playerID, "score")
       DirtySystem.MarkDirty(playerID, "flags")
       DirtySystem.ProcessDirty("score", callback)
]]

local Constants = require("Cheater_Detection.Core.constants")

local next  = next
local pairs = pairs

local DirtySystem = {}

-- Valid dirty reasons (string keys for clarity)
DirtySystem.REASONS = {
    SCORE        = "score",
    FLAGS        = "flags",
    CHECKS       = "checks",
    SESSION      = "session",
    PRIORITY     = "priority",
    CONNECTED    = "connected",
    DISCONNECTED = "disconnected",
}

-- Single table: [playerID] = {reason1=true, reason2=true, ...}
local dirtyPlayers = {}
local dirtyPlayerCount = 0

-- Object pool for per-player reason tables to eliminate GC churn
local entryPool = {}
local entryPoolCount = 0

-- Scratch buffer for re-entrancy-safe ProcessDirty execution
local processBuffer = {}

-- Stats
local stats = {
    marksTotal = 0,
    processesTotal = 0,
}

local function acquireEntry()
    if entryPoolCount > 0 then
        local entry = entryPool[entryPoolCount]
        entryPool[entryPoolCount] = nil
        entryPoolCount = entryPoolCount - 1
        return entry
    end
    return {}
end

local function releaseEntry(playerID, entry)
    dirtyPlayers[playerID] = nil
    dirtyPlayerCount = dirtyPlayerCount - 1
    if entryPoolCount < 128 then
        entryPoolCount = entryPoolCount + 1
        entryPool[entryPoolCount] = entry
    end
end

--- Mark a player as dirty with specific reason
---@param playerID string Player's SteamID64
---@param reason string One of DirtySystem.REASONS
function DirtySystem.MarkDirty(playerID, reason)
    if not playerID or not reason then
        return
    end

    local playerEntry = dirtyPlayers[playerID]
    if not playerEntry then
        playerEntry = acquireEntry()
        dirtyPlayers[playerID] = playerEntry
        dirtyPlayerCount = dirtyPlayerCount + 1
    end

    if not playerEntry[reason] then
        playerEntry[reason] = true
        stats.marksTotal = stats.marksTotal + 1
    end
end

--- Process dirty players for specific reason (safe against re-entrant MarkDirty/ClearDirty inside callback)
---@param reason string One of DirtySystem.REASONS to process
---@param callback function Called for each dirty player: callback(playerID)
function DirtySystem.ProcessDirty(reason, callback)
    if not reason or not callback or dirtyPlayerCount == 0 then
        return 0
    end

    local count = 0

    for playerID, reasons in pairs(dirtyPlayers) do
        if reasons[reason] then
            count = count + 1
            processBuffer[count] = playerID

            -- Clear this reason before running callback so re-entrant marks are preserved
            reasons[reason] = nil

            -- If no more reasons, recycle player entry
            if not next(reasons) then
                releaseEntry(playerID, reasons)
            end
        end
    end

    for i = 1, count do
        local playerID = processBuffer[i]
        processBuffer[i] = nil
        callback(playerID)
    end

    stats.processesTotal = stats.processesTotal + count
    return count
end

--- Check if a player has specific dirty reason
---@param playerID string Player's SteamID64
---@param reason string? One of DirtySystem.REASONS
---@return boolean True if player has this reason dirty
function DirtySystem.IsDirty(playerID, reason)
    if not playerID then
        return false
    end
    local playerEntry = dirtyPlayers[playerID]
    if not playerEntry then
        return false
    end
    if reason then
        return playerEntry[reason] == true
    end
    return next(playerEntry) ~= nil
end

--- Get all dirty reasons for a player
---@param playerID string Player's SteamID64
---@return table|nil Table of reasons {score=true, flags=true} or nil
function DirtySystem.GetDirtyReasons(playerID)
    if not playerID then
        return nil
    end
    return dirtyPlayers[playerID]
end

--- Get all player IDs with specific dirty reason
---@param reason string One of DirtySystem.REASONS
---@param outTable table? Optional pre-allocated array to populate
---@return table Array of player IDs
function DirtySystem.GetDirtyPlayers(reason, outTable)
    local players = outTable or {}
    if outTable then
        for i = 1, #players do
            players[i] = nil
        end
    end
    if not reason or dirtyPlayerCount == 0 then
        return players
    end

    local n = 0
    for playerID, reasons in pairs(dirtyPlayers) do
        if reasons[reason] then
            n = n + 1
            players[n] = playerID
        end
    end

    return players
end

--- Clear dirty reasons for a player
---@param playerID string Player's SteamID64
---@param reason string|nil Specific reason to clear (nil = clear all)
function DirtySystem.ClearDirty(playerID, reason)
    if not playerID then
        return
    end
    local playerEntry = dirtyPlayers[playerID]
    if not playerEntry then
        return
    end

    if not reason then
        -- Clear all and recycle table
        for k in pairs(playerEntry) do
            playerEntry[k] = nil
        end
        releaseEntry(playerID, playerEntry)
    elseif playerEntry[reason] then
        -- Clear specific reason
        playerEntry[reason] = nil
        if not next(playerEntry) then
            releaseEntry(playerID, playerEntry)
        end
    end
end

--- Clear all dirty data
function DirtySystem.ClearAll()
    for playerID, entry in pairs(dirtyPlayers) do
        for k in pairs(entry) do
            entry[k] = nil
        end
        releaseEntry(playerID, entry)
    end
    dirtyPlayerCount = 0
    stats.marksTotal = 0
    stats.processesTotal = 0
end

--- Get statistics
---@return table Statistics
function DirtySystem.GetStats()
    return {
        marksTotal = stats.marksTotal,
        processesTotal = stats.processesTotal,
        dirtyPlayerCount = dirtyPlayerCount,
    }
end

--- Reset statistics counters
function DirtySystem.ResetStats()
    stats.marksTotal = 0
    stats.processesTotal = 0
end

return DirtySystem
