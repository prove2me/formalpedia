-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_hasWeightedSupport_zero_one
-- name    : OAI.PiExponent.FormalInterpolation.hasWeightedSupport_zero_one
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T06:18:20.932065+00:00
-- url     : https://prove2.me/theorems/6e4089d0-b832-4d15-910b-189faf1f3939
-- title:
--   Weighted support of the unit series at threshold zero
-- statement:
--   The constant series one has weighted support at threshold zero for every choice of weights.
-- source:
--   Adapted from formalJet_mem_weighted_of_mem_pow in CompactJetPolynomial.lean, cited by the parent target.

import Definitions.Def_OAI_PiExponent_WeightedSupport

open OAI.PiExponent.FormalInterpolation
open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.hasWeightedSupport_zero_one {m : ℕ} (v : Fin (m + 1) → ℝ) : hasWeightedSupport v 0 (1 : MvPowerSeries (Fin (m + 1)) ℂ) := by sorry
