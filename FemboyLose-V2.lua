local Players = game:GetService("Players")
local RunService = game:GetService("RunService")
local UserInputService = game:GetService("UserInputService")
local Workspace = game:GetService("Workspace")
local Lighting = game:GetService("Lighting")

local LocalPlayer = Players.LocalPlayer
local Camera = Workspace.CurrentCamera

local NEVERLOSE = loadstring(game:HttpGet("https://raw.githubusercontent.com/CludeHub/SourceCludeLib/refs/heads/main/NerverLoseLibEdited.lua"))()
local Window = NEVERLOSE:AddWindow("Femboylose", "HvH & WORLD EDITION", 'original')

-- Global Config
local Config = {
    Aimbot = {
        Enabled = false,
        AlwaysOn = false,
        VisibleCheck = false,
        TargetPart = "Head",
        FOV = 120,
        DrawFOV = false,
        AutoShoot = false,
        ShootDelay = 0.1,
        TargetNPCs = false -- Целиться в ботов (NPC)
    },
    HvH = {
        AntiAim = false,
        Pitch = "Down",
        Yaw = "Spin",
        SpinSpeed = 60,
        FakeLag = false,
        FakeLagLimit = 8
    },
    ESP = {
        Highlight = false,
        HighlightColor = Color3.fromRGB(255, 0, 100),
        HighlightOutline = Color3.fromRGB(255, 255, 255),
        MaterialChams = false,
        ChamsMaterial = "Neon",
        ChamsColor = Color3.fromRGB(255, 0, 128),
        Box = false,
        Name = false,
        Health = false,
        HealthBar = false,
        Distance = false,
        Tracers = false,
        TracerColor = Color3.fromRGB(255, 105, 180),
        ShowNPCs = false -- Показывать ботов (NPC) в ESP
    },
    World = {
        FOV = 70,
        ClockTime = 12,
        FreezeTime = false,
        Brightness = 2,
        Fullbright = false,
        GlobalShadows = true,
        OutdoorAmbient = Color3.fromRGB(128, 128, 128),
        Technology = "ShadowMap",
        NoFog = false,
        FogStart = 0,
        FogEnd = 10000,
        Skybox = "Default",
    },
    ModelChanger = {
        TargetUser = "",
        RemoveAccessories = false,
        CopyClothesOnly = false
    },
    Movement = {
        SpeedHack = false,
        SpeedValue = 32,
        InfJump = false,
        JumpPower = 100,
        Noclip = false,
        BHop = false
    }
}

-- Tabs
Window:AddTabLabel('Combat & Exploits')
local AimTab = Window:AddTab('Ragebot', 'crosshair')
local HvhTab = Window:AddTab('HvH Tools', 'target')

Window:AddTabLabel('Visuals & World')
local EspTab = Window:AddTab('ESP Main', 'box')
local WorldTab = Window:AddTab('World Lighting', 'sun')
local PostTab = Window:AddTab('Post Processing', 'sun')

Window:AddTabLabel('Customization')
local ModelTab = Window:AddTab('Model Changer', 'user')

Window:AddTabLabel('Movement & Misc')
local MoveTab = Window:AddTab('Movement', 'navigation')

-- Sections
local aimSec = AimTab:AddSection('Aimbot Settings', "left")
local aimTargetSec = AimTab:AddSection('Targeting & Checks', "right")

local hvhSec = HvhTab:AddSection('Anti-Aim Angles', "left")
local hvhMiscSec = HvhTab:AddSection('Desync & FakeLag', "right")

local espSec = EspTab:AddSection('Player Visuals', "left")
local espExtraSec = EspTab:AddSection('Overlay & Tracers', "right")

local worldLightingSec = WorldTab:AddSection('Environment & Time', "left")
local worldFogSec = WorldTab:AddSection('Fog & Skybox Controls', "right")

local postEffectSec = PostTab:AddSection('Color Correction & Blur', "left")
local postBloomSec = PostTab:AddSection('Bloom & SunRays', "right")

local modelStealSec = ModelTab:AddSection('Skin Stealer / Morph', "left")
local modelOptSec = ModelTab:AddSection('Morph Options', "right")

local moveSec = MoveTab:AddSection('Main Movement', "left")
local moveMiscSec = MoveTab:AddSection('Physics Helpers', "right")

-- Universal Input Helper
local function AddSafeInput(sec, title, placeholder, callback)
    if typeof(sec.AddInput) == "function" then
        sec:AddInput(title, callback)
    elseif typeof(sec.AddBox) == "function" then
        sec:AddBox(title, callback)
    elseif typeof(sec.AddTextBox) == "function" then
        sec:AddTextBox(title, placeholder or "Text...", callback)
    end
end

-- ==================== RAGEBOT ====================
aimSec:AddToggle('Enable Ragebot', false, function(v) Config.Aimbot.Enabled = v end)
aimSec:AddToggle('Always On', false, function(v) Config.Aimbot.AlwaysOn = v end)
aimSec:AddToggle('Auto Shoot', false, function(v) Config.Aimbot.AutoShoot = v end)

aimTargetSec:AddDropdown('Target Part', {'Head', 'HumanoidRootPart'}, 'Head', function(v) Config.Aimbot.TargetPart = v end)
aimTargetSec:AddToggle('Target NPCs / Bots', false, function(v) Config.Aimbot.TargetNPCs = v end)
aimTargetSec:AddToggle('Visible Check', false, function(v) Config.Aimbot.VisibleCheck = v end)
aimTargetSec:AddSlider('Aimbot FOV', 10, 800, 120, function(v) Config.Aimbot.FOV = v end)
aimTargetSec:AddToggle('Draw FOV Circle', false, function(v) Config.Aimbot.DrawFOV = v end)

local FOVCircle = nil
if Drawing then
    FOVCircle = Drawing.new("Circle")
    FOVCircle.Thickness = 1.5
    FOVCircle.NumSides = 64
    FOVCircle.Filled = false
    FOVCircle.Transparency = 0.8
    FOVCircle.Color = Color3.fromRGB(255, 0, 100)
    FOVCircle.Visible = false
end

local function IsVisible(part)
    local castParams = RaycastParams.new()
    castParams.FilterType = Enum.RaycastFilterType.Exclude
    castParams.FilterDescendantsInstances = {LocalPlayer.Character, Camera}
    local res = Workspace:Raycast(Camera.CFrame.Position, part.Position - Camera.CFrame.Position, castParams)
    return res and res.Instance:IsDescendantOf(part.Parent)
end

local function GetClosestTarget()
    local closest, minDistance = nil, Config.Aimbot.FOV
    local center = Vector2.new(Camera.ViewportSize.X / 2, Camera.ViewportSize.Y / 2)

    local targets = {}

    -- Игроки
    for _, plr in pairs(Players:GetPlayers()) do
        if plr ~= LocalPlayer and plr.Character then
            table.insert(targets, plr.Character)
        end
    end

    -- Боты / NPC
    if Config.Aimbot.TargetNPCs then
        for _, obj in pairs(Workspace:GetChildren()) do
            if obj:IsA("Model") and obj ~= LocalPlayer.Character and not Players:GetPlayerFromCharacter(obj) then
                if obj:FindFirstChildOfClass("Humanoid") then
                    table.insert(targets, obj)
                end
            end
        end
    end

    for _, char in pairs(targets) do
        local part = char:FindFirstChild(Config.Aimbot.TargetPart)
        local hum = char:FindFirstChildOfClass("Humanoid")
        if part and hum and hum.Health > 0 then
            if Config.Aimbot.VisibleCheck and not IsVisible(part) then continue end
            local screenPos, onScreen = Camera:WorldToViewportPoint(part.Position)
            if onScreen then
                local dist = (Vector2.new(screenPos.X, screenPos.Y) - center).Magnitude
                if dist < minDistance then
                    minDistance = dist
                    closest = part
                end
            end
        end
    end
    return closest
end

local function SafeShoot()
    local char = LocalPlayer.Character
    if char then
        local tool = char:FindFirstChildOfClass("Tool")
        if tool then
            tool:Activate()
        end
    end
end

local lastShotTime = 0

RunService.RenderStepped:Connect(function()
    if FOVCircle then
        FOVCircle.Visible = Config.Aimbot.Enabled and Config.Aimbot.DrawFOV
        if FOVCircle.Visible then
            FOVCircle.Position = Vector2.new(Camera.ViewportSize.X / 2, Camera.ViewportSize.Y / 2)
            FOVCircle.Radius = Config.Aimbot.FOV
        end
    end

    if Config.Aimbot.Enabled then
        local active = Config.Aimbot.AlwaysOn or UserInputService:IsMouseButtonPressed(Enum.UserInputType.MouseButton2) or UserInputService:IsMouseButtonPressed(Enum.UserInputType.Touch)
        if active then
            local target = GetClosestTarget()
            if target then
                Camera.CFrame = CFrame.lookAt(Camera.CFrame.Position, target.Position)
                
                if Config.Aimbot.AutoShoot and (tick() - lastShotTime >= Config.Aimbot.ShootDelay) then
                    lastShotTime = tick()
                    pcall(SafeShoot)
                end
            end
        end
    end
end)

-- ==================== ANTI-AIM & HVH ====================
hvhSec:AddToggle('Enable Anti-Aim', false, function(v) Config.HvH.AntiAim = v end)
hvhSec:AddDropdown('Pitch Mode', {'Down', 'Up', 'Zero'}, 'Down', function(v) Config.HvH.Pitch = v end)
hvhSec:AddDropdown('Yaw Mode', {'Spin', 'Jitter', 'Backward'}, 'Spin', function(v) Config.HvH.Yaw = v end)
hvhSec:AddSlider('Spin Speed', 10, 180, 60, function(v) Config.HvH.SpinSpeed = v end)

hvhMiscSec:AddToggle('Enable FakeLag', false, function(v) Config.HvH.FakeLag = v end)
hvhMiscSec:AddSlider('FakeLag Limit', 2, 20, 8, function(v) Config.HvH.FakeLagLimit = v end)

local aaAngle = 0
RunService.RenderStepped:Connect(function()
    local char = LocalPlayer.Character
    if Config.HvH.AntiAim and char then
        local root = char:FindFirstChild("HumanoidRootPart")
        local hum = char:FindFirstChildOfClass("Humanoid")
        if root and hum then
            hum.AutoRotate = false
            
            local pitchAngle = 0
            if Config.HvH.Pitch == "Down" then pitchAngle = math.rad(-89)
            elseif Config.HvH.Pitch == "Up" then pitchAngle = math.rad(89) end

            if Config.HvH.Yaw == "Spin" then
                aaAngle = (aaAngle + Config.HvH.SpinSpeed) % 360
            elseif Config.HvH.Yaw == "Jitter" then
                aaAngle = (aaAngle + 180 + math.random(-45, 45)) % 360
            elseif Config.HvH.Yaw == "Backward" then
                aaAngle = (Camera.CFrame.LookVector.Y * 180) + 180
            end

            root.CFrame = CFrame.new(root.Position) * CFrame.Angles(pitchAngle, math.rad(aaAngle), 0)
        end
    elseif char and char:FindFirstChildOfClass("Humanoid") then
        char:FindFirstChildOfClass("Humanoid").AutoRotate = true
    end
end)

local fakeLagCounter = 0
RunService.Heartbeat:Connect(function()
    if Config.HvH.FakeLag and LocalPlayer.Character and LocalPlayer.Character:FindFirstChild("HumanoidRootPart") then
        fakeLagCounter = fakeLagCounter + 1
        if fakeLagCounter <= Config.HvH.FakeLagLimit then
            LocalPlayer.Character.HumanoidRootPart.Anchored = true
        else
            LocalPlayer.Character.HumanoidRootPart.Anchored = false
            fakeLagCounter = 0
        end
    end
end)

-- ==================== ESP & VISUALS ====================
espSec:AddToggle('Show NPCs / Bots', false, function(v) Config.ESP.ShowNPCs = v end)
espSec:AddToggle('Highlight Glow', false, function(v) Config.ESP.Highlight = v end)
espSec:AddDropdown('Glow Color', {'Pink', 'Red', 'Green', 'Blue', 'Cyan', 'Purple'}, 'Pink', function(v)
    local colors = {Pink=Color3.fromRGB(255,0,128), Red=Color3.fromRGB(255,0,0), Green=Color3.fromRGB(0,255,0), Blue=Color3.fromRGB(0,120,255), Cyan=Color3.fromRGB(0,255,255), Purple=Color3.fromRGB(180,0,255)}
    Config.ESP.HighlightColor = colors[v] or colors.Pink
end)

espSec:AddToggle('Material Chams', false, function(v) Config.ESP.MaterialChams = v end)
espSec:AddDropdown('Chams Material', {'Neon', 'ForceField', 'Glass', 'SmoothPlastic'}, 'Neon', function(v) Config.ESP.ChamsMaterial = v end)

espExtraSec:AddToggle('Name ESP', false, function(v) Config.ESP.Name = v end)
espExtraSec:AddToggle('Health Text', false, function(v) Config.ESP.Health = v end)
espExtraSec:AddToggle('Health Bar', false, function(v) Config.ESP.HealthBar = v end)
espExtraSec:AddToggle('Distance ESP', false, function(v) Config.ESP.Distance = v end)
espExtraSec:AddToggle('Tracers (Lines)', false, function(v) Config.ESP.Tracers = v end)

local TracerLines = {}
local OrigProps = {}

local function ClearTracer(key)
    if TracerLines[key] then TracerLines[key]:Remove() TracerLines[key] = nil end
end

local function GetESPTargets()
    local targets = {}
    
    -- Игроки
    for _, plr in pairs(Players:GetPlayers()) do
        if plr ~= LocalPlayer and plr.Character then
            table.insert(targets, {Character = plr.Character, Name = plr.Name})
        end
    end

    -- Боты / NPC
    if Config.ESP.ShowNPCs then
        for _, obj in pairs(Workspace:GetChildren()) do
            if obj:IsA("Model") and obj ~= LocalPlayer.Character and not Players:GetPlayerFromCharacter(obj) then
                local hum = obj:FindFirstChildOfClass("Humanoid")
                if hum then
                    table.insert(targets, {Character = obj, Name = obj.Name .. " [NPC]"})
                end
            end
        end
    end

    return targets
end

RunService.RenderStepped:Connect(function()
    local currentTargets = GetESPTargets()
    local activeChars = {}

    for _, targetData in pairs(currentTargets) do
        local char = targetData.Character
        activeChars[char] = true

        local head = char:FindFirstChild("Head")
        local root = char:FindFirstChild("HumanoidRootPart") or head
        local hum = char:FindFirstChildOfClass("Humanoid")

        local hl = char:FindFirstChild("FemboyGlow")
        if Config.ESP.Highlight then
            if not hl then
                hl = Instance.new("Highlight")
                hl.Name = "FemboyGlow"
                hl.Parent = char
            end
            hl.FillColor = Config.ESP.HighlightColor
            hl.DepthMode = Enum.HighlightDepthMode.AlwaysOnTop
        elseif hl then hl:Destroy() end

        if Config.ESP.MaterialChams then
            for _, part in pairs(char:GetChildren()) do
                if part:IsA("BasePart") and part.Name ~= "HumanoidRootPart" then
                    if not OrigProps[part] then OrigProps[part] = {Material = part.Material, Color = part.Color} end
                    part.Material = Enum.Material[Config.ESP.ChamsMaterial] or Enum.Material.Neon
                    part.Color = Config.ESP.HighlightColor
                end
            end
        else
            for part, props in pairs(OrigProps) do
                if part and part.Parent then
                    part.Material = props.Material
                    part.Color = props.Color
                end
            end
            table.clear(OrigProps)
        end

        if head and hum and hum.Health > 0 then
            local bbg = head:FindFirstChild("FemboyESP")
            if not bbg then
                bbg = Instance.new("BillboardGui", head)
                bbg.Name = "FemboyESP"
                bbg.Size = UDim2.new(0, 140, 0, 60)
                bbg.StudsOffset = Vector3.new(0, 2.8, 0)
                bbg.AlwaysOnTop = true
                
                local txt = Instance.new("TextLabel", bbg)
                txt.Name = "Label"
                txt.Size = UDim2.new(1, 0, 0.7, 0)
                txt.BackgroundTransparency = 1
                txt.TextColor3 = Color3.fromRGB(255, 255, 255)
                txt.TextStrokeTransparency = 0
                txt.Font = Enum.Font.SourceSansBold
                txt.TextSize = 10

                local hpBG = Instance.new("Frame", bbg)
                hpBG.Name = "HPBG"
                hpBG.Size = UDim2.new(0.8, 0, 0, 3)
                hpBG.Position = UDim2.new(0.1, 0, 0.8, 0)
                hpBG.BackgroundColor3 = Color3.fromRGB(30, 30, 30)
                hpBG.BorderSizePixel = 0

                local hpBar = Instance.new("Frame", hpBG)
                hpBar.Name = "Bar"
                hpBar.Size = UDim2.new(1, 0, 1, 0)
                hpBar.BackgroundColor3 = Color3.fromRGB(0, 255, 100)
                hpBar.BorderSizePixel = 0
            end

            local str = ""
            if Config.ESP.Name then str = str .. targetData.Name .. "\n" end
            if Config.ESP.Health then str = str .. "HP: " .. math.floor(hum.Health) .. " " end
            if Config.ESP.Distance and root then
                local d = math.floor((root.Position - Camera.CFrame.Position).Magnitude)
                str = str .. "[" .. d .. "m]"
            end
            bbg.Label.Text = str

            if Config.ESP.HealthBar then
                bbg.HPBG.Visible = true
                local hpPct = math.clamp(hum.Health / hum.MaxHealth, 0, 1)
                bbg.HPBG.Bar.Size = UDim2.new(hpPct, 0, 1, 0)
                bbg.HPBG.Bar.BackgroundColor3 = Color3.fromRGB(255,0,0):Lerp(Color3.fromRGB(0,255,100), hpPct)
            else
                bbg.HPBG.Visible = false
            end
        end

        if Config.ESP.Tracers and root and Drawing then
            local screenPos, onScreen = Camera:WorldToViewportPoint(root.Position)
            if onScreen then
                if not TracerLines[char] then
                    TracerLines[char] = Drawing.new("Line")
                    TracerLines[char].Thickness = 1.5
                    TracerLines[char].Transparency = 0.8
                end
                TracerLines[char].Color = Config.ESP.TracerColor
                TracerLines[char].From = Vector2.new(Camera.ViewportSize.X / 2, Camera.ViewportSize.Y)
                TracerLines[char].To = Vector2.new(screenPos.X, screenPos.Y)
                TracerLines[char].Visible = true
            else ClearTracer(char) end
        else ClearTracer(char) end
    end

    for char, _ in pairs(TracerLines) do
        if not activeChars[char] or not char:IsDescendantOf(Workspace) then
            ClearTracer(char)
        end
    end
end)

-- ==================== WORLD SETTINGS ====================
worldLightingSec:AddSlider('Field Of View (FOV)', 30, 120, 70, function(v)
    Config.World.FOV = v
    Camera.FieldOfView = v
end)

worldLightingSec:AddSlider('Time of Day', 0, 24, 12, function(v)
    Config.World.ClockTime = v
    Lighting.ClockTime = v
end)

worldLightingSec:AddToggle('Freeze Time', false, function(v) Config.World.FreezeTime = v end)

worldLightingSec:AddSlider('Brightness', 0, 10, 2, function(v)
    Config.World.Brightness = v
    Lighting.Brightness = v
end)

worldLightingSec:AddToggle('Fullbright', false, function(v)
    Config.World.Fullbright = v
    if v then
        Lighting.Ambient = Color3.fromRGB(255, 255, 255)
        Lighting.OutdoorAmbient = Color3.fromRGB(255, 255, 255)
    end
end)

worldLightingSec:AddToggle('Global Shadows', true, function(v)
    Config.World.GlobalShadows = v
    Lighting.GlobalShadows = v
end)

worldLightingSec:AddDropdown('Lighting Technology', {'ShadowMap', 'Compatibility', 'Future'}, 'ShadowMap', function(v)
    pcall(function() Lighting.Technology = Enum.Technology[v] end)
end)

worldFogSec:AddToggle('Disable Fog', false, function(v)
    Config.World.NoFog = v
    Lighting.FogEnd = v and 9e9 or Config.World.FogEnd
end)

worldFogSec:AddSlider('Fog Start', 0, 5000, 0, function(v)
    Config.World.FogStart = v
    if not Config.World.NoFog then Lighting.FogStart = v end
end)

worldFogSec:AddSlider('Fog End', 500, 20000, 10000, function(v)
    Config.World.FogEnd = v
    if not Config.World.NoFog then Lighting.FogEnd = v end
end)

local SkyTextures = {
    ['Purple CS:GO'] = {Bk="rbxassetid://159454299", Ft="rbxassetid://159454296", Lf="rbxassetid://159454293", Rt="rbxassetid://159454300", Up="rbxassetid://159454302", Dn="rbxassetid://159454288"},
    ['Night Sky']   = {Bk="rbxassetid://12064107", Ft="rbxassetid://12064121", Lf="rbxassetid://12064116", Rt="rbxassetid://12064110", Up="rbxassetid://12064131", Dn="rbxassetid://12064096"},
    ['Space']       = {Bk="rbxassetid://266205880", Ft="rbxassetid://266205880", Lf="rbxassetid://266205880", Rt="rbxassetid://266205880", Up="rbxassetid://266205880", Dn="rbxassetid://266205880"}
}

worldFogSec:AddDropdown('Skybox Preset', {'Default', 'Purple CS:GO', 'Night Sky', 'Space'}, 'Default', function(v)
    local currentSky = Lighting:FindFirstChildOfClass("Sky")
    if v == 'Default' then
        if currentSky then currentSky:Destroy() end
    else
        if not currentSky then
            currentSky = Instance.new("Sky", Lighting)
        end
        local data = SkyTextures[v]
        if data then
            currentSky.SkyboxBk = data.Bk
            currentSky.SkyboxFt = data.Ft
            currentSky.SkyboxLf = data.Lf
            currentSky.SkyboxRt = data.Rt
            currentSky.SkyboxUp = data.Up
            currentSky.SkyboxDn = data.Dn
        end
    end
end)

-- ==================== POST-PROCESSING ====================
local ColorCorrection = Lighting:FindFirstChildOfClass("ColorCorrectionEffect")
if not ColorCorrection then
    ColorCorrection = Instance.new("ColorCorrectionEffect", Lighting)
    ColorCorrection.Saturation = 0
    ColorCorrection.Contrast = 0
end

local Blur = Lighting:FindFirstChildOfClass("BlurEffect")
if not Blur then
    Blur = Instance.new("BlurEffect", Lighting)
    Blur.Size = 0
    Blur.Enabled = false
end

local Bloom = Lighting:FindFirstChildOfClass("BloomEffect")
if not Bloom then
    Bloom = Instance.new("BloomEffect", Lighting)
    Bloom.Intensity = 0
    Bloom.Enabled = false
end

local SunRays = Lighting:FindFirstChildOfClass("SunRaysEffect")
if not SunRays then
    SunRays = Instance.new("SunRaysEffect", Lighting)
    SunRays.Intensity = 0
    SunRays.Enabled = false
end

postEffectSec:AddSlider('Saturation', -100, 100, 0, function(v)
    ColorCorrection.Saturation = v / 50
end)

postEffectSec:AddSlider('Contrast', -100, 100, 0, function(v)
    ColorCorrection.Contrast = v / 50
end)

postEffectSec:AddSlider('Blur Size', 0, 50, 0, function(v)
    Blur.Size = v
    Blur.Enabled = (v > 0)
end)

postBloomSec:AddToggle('Enable Bloom', false, function(v)
    Bloom.Enabled = v
end)

postBloomSec:AddSlider('Bloom Intensity', 0, 10, 1, function(v)
    Bloom.Intensity = v
end)

postBloomSec:AddToggle('Enable SunRays', false, function(v)
    SunRays.Enabled = v
end)

postBloomSec:AddSlider('SunRays Intensity', 0, 10, 2, function(v)
    SunRays.Intensity = v / 10
end)

RunService.RenderStepped:Connect(function()
    if Config.World.FreezeTime then
        Lighting.ClockTime = Config.World.ClockTime
    end
end)

-- ==================== MODEL CHANGER ====================
AddSafeInput(modelStealSec, 'Target Username', 'Enter username...', function(v)
    Config.ModelChanger.TargetUser = tostring(v)
end)

modelOptSec:AddToggle('Remove Accessories First', false, function(v)
    Config.ModelChanger.RemoveAccessories = v
end)

modelOptSec:AddToggle('Copy Clothes Only', false, function(v)
    Config.ModelChanger.CopyClothesOnly = v
end)

modelStealSec:AddButton('Steal Skin / Morph', function()
    local name = Config.ModelChanger.TargetUser
    if name == "" then return end

    task.spawn(function()
        local ok, userId = pcall(function()
            return Players:GetUserIdFromNameAsync(name)
        end)

        if ok and userId then
            local descOk, humDesc = pcall(function()
                return Players:GetHumanoidDescriptionFromUserId(userId)
            end)

            local char = LocalPlayer.Character
            if char and descOk and humDesc then
                local hum = char:FindFirstChildOfClass("Humanoid")
                if hum then
                    if Config.ModelChanger.RemoveAccessories then
                        for _, acc in pairs(char:GetChildren()) do
                            if acc:IsA("Accessory") or acc:IsA("Shirt") or acc:IsA("Pants") or acc:IsA("ShirtGraphic") then
                                acc:Destroy()
                            end
                        end
                    end

                    if Config.ModelChanger.CopyClothesOnly then
                        local currentDesc = hum:GetAppliedDescription()
                        currentDesc.Shirt = humDesc.Shirt
                        currentDesc.Pants = humDesc.Pants
                        currentDesc.Graphic = humDesc.Graphic
                        hum:ApplyDescription(currentDesc)
                    else
                        hum:ApplyDescription(humDesc)
                    end
                end
            end
        end
    end)
end)

modelStealSec:AddButton('Reset Character', function()
    if LocalPlayer.Character and LocalPlayer.Character:FindFirstChildOfClass("Humanoid") then
        LocalPlayer.Character:FindFirstChildOfClass("Humanoid").Health = 0
    end
end)

-- ==================== MOVEMENT ====================
moveSec:AddToggle('Enable SpeedHack', false, function(v)
    Config.Movement.SpeedHack = v
    if LocalPlayer.Character and LocalPlayer.Character:FindFirstChildOfClass("Humanoid") then
        LocalPlayer.Character:FindFirstChildOfClass("Humanoid").WalkSpeed = v and Config.Movement.SpeedValue or 16
    end
end)

moveSec:AddSlider('Speed Value', 16, 300, 32, function(v)
    Config.Movement.SpeedValue = v
    if Config.Movement.SpeedHack and LocalPlayer.Character and LocalPlayer.Character:FindFirstChildOfClass("Humanoid") then
        LocalPlayer.Character:FindFirstChildOfClass("Humanoid").WalkSpeed = v
    end
end)

moveSec:AddToggle('Infinite Jump', false, function(v) Config.Movement.InfJump = v end)
moveSec:AddSlider('Jump Power', 50, 400, 100, function(v) Config.Movement.JumpPower = v end)

moveMiscSec:AddToggle('Noclip', false, function(v) Config.Movement.Noclip = v end)
moveMiscSec:AddToggle('Auto BHop', false, function(v) Config.Movement.BHop = v end)

UserInputService.JumpRequest:Connect(function()
    if Config.Movement.InfJump and LocalPlayer.Character then
        local hum = LocalPlayer.Character:FindFirstChildOfClass("Humanoid")
        local root = LocalPlayer.Character:FindFirstChild("HumanoidRootPart")
        if hum and root then
            hum:ChangeState(Enum.HumanoidStateType.Jumping)
            root.Velocity = Vector3.new(root.Velocity.X, Config.Movement.JumpPower, root.Velocity.Z)
        end
    end
end)

RunService.Stepped:Connect(function()
    if Config.Movement.Noclip and LocalPlayer.Character then
        for _, part in pairs(LocalPlayer.Character:GetDescendants()) do
            if part:IsA("BasePart") then
                part.CanCollide = false
            end
        end
    end

    if Config.Movement.BHop and LocalPlayer.Character then
        local hum = LocalPlayer.Character:FindFirstChildOfClass("Humanoid")
        if hum and hum.FloorMaterial ~= Enum.Material.Air then
            hum:ChangeState(Enum.HumanoidStateType.Jumping)
        end
    end
end)

LocalPlayer.CharacterAdded:Connect(function(char)
    char:WaitForChild("Humanoid")
    if Config.Movement.SpeedHack then
        char.Humanoid.WalkSpeed = Config.Movement.SpeedValue
    end
end)