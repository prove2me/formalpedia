-- Prove2me | Theorems.Thm_Light_sameOutside_wrote
-- name    : Light.sameOutside_wrote
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:19:53.651535+00:00
-- url     : https://prove2.me/theorems/824e49a4-7906-4a08-a285-32e3127e1065
-- title:
--   Light: same Outside wrote
-- statement:
--   Writing `j ≤ n` cells from `dst` changes no cell outside the `n` cells from `dst`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Regions.lean#L165-L166
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Regions.lean#L165-L166

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

theorem Light.sameOutside_wrote {n : ℕ} (h : j ≤ n) : SameOutside μ (wrote μ dst f j) dst n := by sorry
