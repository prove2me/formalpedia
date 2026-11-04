-- Prove2me | Theorems.Thm_Light_Ends_asFrame
-- name    : Light.Ends.asFrame
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:31:54.545065+00:00
-- url     : https://prove2.me/theorems/5bd104bc-139f-42e0-86dc-53f9ec8d7ab6
-- title:
--   Ends: as Frame
-- statement:
--   **From locals that are described by `LocalsBut` to a list.**  The entries `xs` of the list are
--   read from `loc`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Frames.lean#L314-L318
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Frames.lean#L314-L318

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Assigns
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Rules
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Frames
set_option autoImplicit false
public section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
variable {xs : List ℕ} {l l' : List ℤ} {loc μ : ℕ → ℤ}
variable {T T₁ : ℕ} {s s₁ s₂ : Stmt} {Q R : State → Prop}

theorem Light.Ends.asFrame (h : LocalsBut xs l loc)
    (hs : Ends lim P d s ⟨frame (refreshLocals l loc xs), μ⟩ T Q) :
    Ends lim P d s ⟨loc, μ⟩ T Q := by sorry
