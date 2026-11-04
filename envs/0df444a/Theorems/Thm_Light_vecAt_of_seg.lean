-- Prove2me | Theorems.Thm_Light_vecAt_of_seg
-- name    : Light.vecAt_of_seg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:35:16.529658+00:00
-- url     : https://prove2.me/theorems/c91dce0c-a5b2-472c-bd1a-6abb3348b231
-- title:
--   Light: vec At of seg
-- statement:
--   A vector of indices that has been written as a list.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/Seg.lean#L225-L228
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/Seg.lean#L225-L228

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Logic
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Regions
public import Definitions.Def_Submission_ThreeSumApsp_Util_Index
public import Definitions.Def_Submission_ThreeSumApsp_Util_List
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.SuccPred
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Tactic.Positivity
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
set_option autoImplicit false
public section
open Light
open ThreeSumApsp
variable {μ μ' μ'' : ℕ → ℤ} {a b n : ℕ} {l l₁ l₂ : List ℤ} {x : ℤ}

theorem Light.vecAt_of_seg {t n : ℕ} {I : Fin t → Fin n}
    (h : Seg μ a (List.ofFn fun k => ((I k).val : ℤ))) : VecAt μ a I := by sorry
