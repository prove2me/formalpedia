-- Prove2me | Theorems.Thm_Light_wrote_zero
-- name    : Light.wrote_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:19:48.080474+00:00
-- url     : https://prove2.me/theorems/eea35fc3-341c-44ab-81b2-4553165fe563
-- title:
--   Light: wrote zero
-- statement:
--   Nothing has been written yet.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Regions.lean#L128-L131
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Regions.lean#L128-L131

module
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Logic.Function.Basic
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Regions
set_option autoImplicit false
public section
open Light
variable {K K' K₁ K₂ : ℕ → Prop} {μ μ' μ'' : ℕ → ℤ} {b : ℕ}
variable {dst j : ℕ} {f : ℕ → ℤ}

theorem Light.wrote_zero : wrote μ dst f 0 = μ := by sorry
