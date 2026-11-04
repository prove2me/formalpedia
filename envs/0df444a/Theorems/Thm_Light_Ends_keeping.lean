-- Prove2me | Theorems.Thm_Light_Ends_keeping
-- name    : Light.Ends.keeping
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:25:53.871424+00:00
-- url     : https://prove2.me/theorems/0b1bea44-119b-41a9-80e7-0bb7a02aa9e9
-- title:
--   Ends: keeping
-- statement:
--   **All other locals are as before.**  Whatever holds after a statement, it also holds that the
--   locals that the statement does not assign are unchanged.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Assigns.lean#L55-L59
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Assigns.lean#L55-L59

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Logic
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Assigns
set_option autoImplicit false
public section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}

theorem Light.Ends.keeping {s : Stmt} {σ : State} {T : ℕ} {Q : State → Prop}
    (h : Ends lim P d s σ T Q) :
    Ends lim P d s σ T fun σ' => Q σ' ∧ ∀ y ∉ s.assigns, σ'.loc y = σ.loc y := by sorry
