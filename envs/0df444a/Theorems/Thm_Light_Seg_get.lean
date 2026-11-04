-- Prove2me | Theorems.Thm_Light_Seg_get
-- name    : Light.Seg.get
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:26:01.572038+00:00
-- url     : https://prove2.me/theorems/64c7599d-8457-4f62-9b8b-d9a36509256e
-- title:
--   Seg: get
-- statement:
--   Reading a cell of a segment.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/Seg.lean#L55-L55
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/Seg.lean#L55-L55

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

theorem Light.Seg.get (h : Seg μ a l) {i : ℕ} (hi : i < l.length) : μ (a + i) = l[i] := by sorry
