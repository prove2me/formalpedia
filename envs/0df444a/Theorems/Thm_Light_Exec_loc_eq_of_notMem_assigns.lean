-- Prove2me | Theorems.Thm_Light_Exec_loc_eq_of_notMem_assigns
-- name    : Light.Exec.loc_eq_of_notMem_assigns
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:25:50.18818+00:00
-- url     : https://prove2.me/theorems/5552e9d6-82f9-41f8-9402-24bd020406a2
-- title:
--   Exec: loc eq of not Mem assigns
-- statement:
--   A run leaves a local variable that the statement does not assign as it was.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Assigns.lean#L38-L51
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Assigns.lean#L38-L51

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Logic
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Assigns
set_option autoImplicit false
public section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}

theorem Light.Exec.loc_eq_of_notMem_assigns {s : Stmt} {σ σ' : State} {c y : ℕ}
    (h : Exec lim P d s σ σ' c) (hy : y ∉ s.assigns) : σ'.loc y = σ.loc y := by sorry
