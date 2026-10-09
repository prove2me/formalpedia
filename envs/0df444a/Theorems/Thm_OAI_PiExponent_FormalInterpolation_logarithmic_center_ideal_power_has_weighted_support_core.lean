-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmic_center_ideal_power_has_weighted_support_core
-- name    : OAI.PiExponent.FormalInterpolation.logarithmic_center_ideal_power_has_weighted_support_core
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-08T18:16:50.372761+00:00
-- url     : https://prove2.me/theorems/2851cc48-2532-4a83-80b7-cb03efb24723
-- title:
--   Filtered support bound for logarithmic center ideal powers
-- statement:
--   For every polynomial in the nth power of the logarithmic center ideal, its formal logarithmic jet has no nonzero coefficient of weighted degree below nR. The condition on the truncation lengths ensures that each logarithmic coordinate contributes at least the corresponding variable weight; the exponent bounds then give the factor R for each ideal generator.
-- source:
--   Adapted from formalJet_mem_weighted_of_mem_pow in CompactJetPolynomial.lean, cited by the parent target.

import Definitions.Def_OAI_PiExponent_LogarithmicCenterIdeals
import Definitions.Def_OAI_PiExponent_WeightedSupport

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem OAI.PiExponent.FormalInterpolation.logarithmic_center_ideal_power_has_weighted_support_core
    {m : ℕ} (c : Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m + 1) → ℕ) (v : Fin (m + 1) → ℝ)
    (hv : ∀ i, 0 ≤ v i)
    (hT : ∀ i, v i.succ ≤ (T i : ℝ) * v 0)
    (R : ℝ) (he : ∀ i, R ≤ (e i : ℝ) * v i)
    (n : ℕ) (P : MvPolynomial (Fin (m + 1)) ℂ)
    (hP : P ∈ FormalInterpolation.logarithmicCenterIdeal c T e ^ n) :
    FormalInterpolation.hasWeightedSupport v ((n : ℝ) * R)
      (FormalInterpolation.formalJet c P) := by sorry
