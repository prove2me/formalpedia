-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_hasWeightedSupport_add
-- name    : OAI.PiExponent.FormalInterpolation.hasWeightedSupport_add
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T05:55:02.872357+00:00
-- url     : https://prove2.me/theorems/667a9393-1047-4675-b5ac-e95d63cd8ba1
-- title:
--   Weighted support is preserved by addition
-- statement:
--   If both series have weighted support at least B, then their sum does too.
-- source:
--   Adapted from formalJet_mem_weighted_of_mem_pow in CompactJetPolynomial.lean, cited by the parent target.

import Definitions.Def_OAI_PiExponent_WeightedSupport

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem OAI.PiExponent.FormalInterpolation.hasWeightedSupport_add
    {m : ℕ} (v : Fin (m + 1) → ℝ) (B : ℝ)
    (F G : MvPowerSeries (Fin (m + 1)) ℂ)
    (hF : FormalInterpolation.hasWeightedSupport v B F)
    (hG : FormalInterpolation.hasWeightedSupport v B G) :
    FormalInterpolation.hasWeightedSupport v B (F + G) := by sorry
