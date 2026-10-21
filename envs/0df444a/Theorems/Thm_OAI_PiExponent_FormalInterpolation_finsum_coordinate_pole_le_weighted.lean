-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_finsum_coordinate_pole_le_weighted
-- name    : OAI.PiExponent.FormalInterpolation.finsum_coordinate_pole_le_weighted
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-21T04:24:23.978495+00:00
-- url     : https://prove2.me/theorems/5e7080a2-3c0d-4df2-b15f-caa67c7ddb1e
-- title:
--   Finite-support comparison for coordinate and weighted pole sums
-- statement:
--   For finitely supported real-valued functions, a pointwise nonnegative bound by a nonnegative constant times another function implies the corresponding finitary-sum inequality.

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Real.Basic

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.finsum_coordinate_pole_le_weighted {α : Type} (c : Real) (hc : 0 ≤ c) (f g : α → Real) (hf : Set.Finite {a | f a ≠ 0}) (hg : Set.Finite {a | g a ≠ 0}) (hfg : ∀ a, 0 ≤ f a ∧ f a ≤ c * g a) : (∑ᶠ a, f a) ≤ c * (∑ᶠ a, g a) := by sorry
