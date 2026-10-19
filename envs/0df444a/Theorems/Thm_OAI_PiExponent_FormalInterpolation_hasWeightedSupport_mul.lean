-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_hasWeightedSupport_mul
-- name    : OAI.PiExponent.FormalInterpolation.hasWeightedSupport_mul
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T05:55:24.951536+00:00
-- url     : https://prove2.me/theorems/4ddcf1bb-c84a-48cc-b239-fffec75a9558
-- title:
--   Weighted support bounds add under multiplication
-- statement:
--   If two series have weighted support at least B and C, respectively, their product has weighted support at least B+C.
-- source:
--   Adapted from formalJet_mem_weighted_of_mem_pow in CompactJetPolynomial.lean, cited by the parent target.

import Definitions.Def_OAI_PiExponent_WeightedSupport

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem OAI.PiExponent.FormalInterpolation.hasWeightedSupport_mul
    {m : ℕ} (v : Fin (m + 1) → ℝ) (B C : ℝ)
    (F G : MvPowerSeries (Fin (m + 1)) ℂ)
    (hF : FormalInterpolation.hasWeightedSupport v B F)
    (hG : FormalInterpolation.hasWeightedSupport v C G) :
    FormalInterpolation.hasWeightedSupport v (B + C) (F * G) := by sorry
