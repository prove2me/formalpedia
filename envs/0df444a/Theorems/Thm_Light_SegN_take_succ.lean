-- Prove2me | Theorems.Thm_Light_SegN_take_succ
-- name    : Light.SegN.take_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:34:23.743128+00:00
-- url     : https://prove2.me/theorems/a9214bfe-8242-46a6-b075-b853848ff5f3
-- title:
--   Seg N: take succ
-- statement:
--   One more entry of a list of natural numbers is written behind its first k entries.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/Seg.lean#L179-L182
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/Seg.lean#L179-L182

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

theorem Light.SegN.take_succ {l : List ℕ} {k : ℕ} (h : SegN μ a (l.take k)) (hk : k < l.length) :
    SegN (Function.update μ (a + k) ((l.getD k 0 : ℕ) : ℤ)) a (l.take (k + 1)) := by sorry
