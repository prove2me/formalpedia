-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_hasWeightedSupport_mul_closure
-- name    : OAI.PiExponent.FormalInterpolation.hasWeightedSupport_mul_closure
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T06:15:06.760223+00:00
-- url     : https://prove2.me/theorems/26e4ab4c-85bf-4d73-8d1a-a2cbdc380715
-- title:
--   Multiplication combines weighted support bounds
-- statement:
--   Multiplying a series supported at weight at least zero by one supported at weight at least B preserves the B support bound.
-- source:
--   Adapted from formalJet_mem_weighted_of_mem_pow in CompactJetPolynomial.lean, cited by the parent target.

import Definitions.Def_OAI_PiExponent_WeightedSupport

open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.hasWeightedSupport_mul_closure {m : ℕ} (v : Fin (m + 1) → ℝ) (B : ℝ) (F G : MvPowerSeries (Fin (m + 1)) ℂ) (hF : hasWeightedSupport v 0 F) (hG : hasWeightedSupport v B G) : hasWeightedSupport v B (F * G) := by sorry
