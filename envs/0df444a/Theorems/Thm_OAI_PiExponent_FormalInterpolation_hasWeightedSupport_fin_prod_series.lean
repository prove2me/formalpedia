-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_hasWeightedSupport_fin_prod_series
-- name    : OAI.PiExponent.FormalInterpolation.hasWeightedSupport_fin_prod_series
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T06:10:01.254288+00:00
-- url     : https://prove2.me/theorems/e452a46e-4857-4414-a5e4-b6f9aee15f54
-- title:
--   Weighted support of finite products of series
-- statement:
--   A finite product of n multivariate power series, each with weighted support at least R, has weighted support at least nR. The empty product case is included.
-- source:
--   Adapted from formalJet_mem_weighted_of_mem_pow in CompactJetPolynomial.lean, cited by the parent target.

import Definitions.Def_OAI_PiExponent_WeightedSupport

open OAI.PiExponent.FormalInterpolation
open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.hasWeightedSupport_fin_prod_series {m : ℕ} (v : Fin (m + 1) → ℝ) (R : ℝ) (n : ℕ) (s : Fin n → MvPowerSeries (Fin (m + 1)) ℂ) (hs : ∀ i, hasWeightedSupport v R (s i)) : hasWeightedSupport v ((n : ℝ) * R) (∏ i, s i) := by sorry
