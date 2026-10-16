-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_hasWeightedSupport_add_closure
-- name    : OAI.PiExponent.FormalInterpolation.hasWeightedSupport_add_closure
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T06:14:53.26099+00:00
-- url     : https://prove2.me/theorems/4cc12540-0287-446c-afe1-b0d37dba7f1d
-- title:
--   Addition preserves weighted support
-- statement:
--   Adding two series whose nonzero coefficients have weight at least B preserves that support bound.
-- source:
--   Adapted from formalJet_mem_weighted_of_mem_pow in CompactJetPolynomial.lean, cited by the parent target.

import Definitions.Def_OAI_PiExponent_WeightedSupport

open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.hasWeightedSupport_add_closure {m : ℕ} (v : Fin (m + 1) → ℝ) (B : ℝ) (F G : MvPowerSeries (Fin (m + 1)) ℂ) (hF : hasWeightedSupport v B F) (hG : hasWeightedSupport v B G) : hasWeightedSupport v B (F + G) := by sorry
