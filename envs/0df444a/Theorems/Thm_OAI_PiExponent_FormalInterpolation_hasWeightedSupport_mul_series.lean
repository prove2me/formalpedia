-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_hasWeightedSupport_mul_series
-- name    : OAI.PiExponent.FormalInterpolation.hasWeightedSupport_mul_series
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T06:18:34.901242+00:00
-- url     : https://prove2.me/theorems/0f1be8f7-f777-46fb-96e7-851ebbd83a89
-- title:
--   Weighted support thresholds add under series multiplication
-- statement:
--   If two multivariate power series have weighted support thresholds A and B, their product has threshold A + B.
-- source:
--   Adapted from formalJet_mem_weighted_of_mem_pow in CompactJetPolynomial.lean, cited by the parent target.

import Definitions.Def_OAI_PiExponent_WeightedSupport

open OAI.PiExponent.FormalInterpolation
open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.hasWeightedSupport_mul_series {m : ℕ} (v : Fin (m + 1) → ℝ) (A B : ℝ) (F G : MvPowerSeries (Fin (m + 1)) ℂ) (hF : hasWeightedSupport v A F) (hG : hasWeightedSupport v B G) : hasWeightedSupport v (A + B) (F * G) := by sorry
