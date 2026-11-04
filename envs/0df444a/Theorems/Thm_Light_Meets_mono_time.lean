-- Prove2me | Theorems.Thm_Light_Meets_mono_time
-- name    : Light.Meets.mono_time
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:33:13.131522+00:00
-- url     : https://prove2.me/theorems/7fc0220a-aa29-4589-b1fd-52a0fece95ec
-- title:
--   Meets: mono time
-- statement:
--   A specification holds with every larger bound on the time.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Calls.lean#L62-L64
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Calls.lean#L62-L64

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Frames
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Calls
set_option autoImplicit false
public section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
variable {p : ℕ} {vals : List ℤ} {μ : ℕ → ℤ} {T T' : ℕ} {R R' : ℤ → (ℕ → ℤ) → Prop}

theorem Light.Meets.mono_time (h : Meets lim P p d vals μ T R) (hT : T ≤ T' := by omega) :
    Meets lim P p d vals μ T' R := by sorry
