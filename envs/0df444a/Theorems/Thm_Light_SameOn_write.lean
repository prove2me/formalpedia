-- Prove2me | Theorems.Thm_Light_SameOn_write
-- name    : Light.SameOn.write
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:19:47.023528+00:00
-- url     : https://prove2.me/theorems/43464ad1-2750-4ea4-8ec9-8bd84b68e6a5
-- title:
--   Same On: write
-- statement:
--   Writing a cell that need not be kept.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Regions.lean#L115-L117
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Regions.lean#L115-L117

module
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Logic.Function.Basic
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Regions
set_option autoImplicit false
public section
open Light
variable {K K' K₁ K₂ : ℕ → Prop} {μ μ' μ'' : ℕ → ℤ} {b : ℕ}

theorem Light.SameOn.write (h : SameOn K μ μ') (hb : ¬ K b) (x : ℤ) :
    SameOn K μ (Function.update μ' b x) := by sorry
