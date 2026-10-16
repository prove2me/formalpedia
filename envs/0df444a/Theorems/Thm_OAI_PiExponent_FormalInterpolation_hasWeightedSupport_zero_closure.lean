-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_hasWeightedSupport_zero_closure
-- name    : OAI.PiExponent.FormalInterpolation.hasWeightedSupport_zero_closure
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T06:14:35.352642+00:00
-- url     : https://prove2.me/theorems/665f7bb0-65bc-49fc-923a-36dfce14ed33
-- title:
--   Zero series has every weighted support bound
-- statement:
--   The zero multivariate power series satisfies every weighted support bound.
-- source:
--   Adapted from formalJet_mem_weighted_of_mem_pow in CompactJetPolynomial.lean, cited by the parent target.

import Definitions.Def_OAI_PiExponent_WeightedSupport

open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.hasWeightedSupport_zero_closure {m : ℕ} (v : Fin (m + 1) → ℝ) (B : ℝ) : hasWeightedSupport v B (0 : MvPowerSeries (Fin (m + 1)) ℂ) := by sorry
