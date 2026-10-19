-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_ideal_power_has_weighted_support_of_generators_nonnegative
-- name    : OAI.PiExponent.FormalInterpolation.ideal_power_has_weighted_support_of_generators_nonnegative
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T05:42:47.088819+00:00
-- url     : https://prove2.me/theorems/6fdafc6d-f343-4991-b8e0-56afa8dfaad3
-- title:
--   Weighted support of powers of ideals with nonnegative weights
-- statement:
--   For nonnegative variable weights, if a ring homomorphism maps every polynomial to a series supported in weighted degree at least zero and maps each ideal generator to a series supported in degree at least R, then elements of the nth power of the generated ideal map to series supported in degree at least nR.
-- source:
--   Adapted from formalJet_mem_weighted_of_mem_pow in CompactJetPolynomial.lean, cited by the parent target.

import Definitions.Def_OAI_PiExponent_WeightedSupport
import Mathlib.RingTheory.Ideal.Operations

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem OAI.PiExponent.FormalInterpolation.ideal_power_has_weighted_support_of_generators_nonnegative
    {m : ℕ} (v : Fin (m + 1) → ℝ)
    (hv : ∀ i, 0 ≤ v i)
    (R : ℝ) (n : ℕ)
    (f : MvPolynomial (Fin (m + 1)) ℂ →+*
      MvPowerSeries (Fin (m + 1)) ℂ)
    (x : Fin (m + 1) → MvPolynomial (Fin (m + 1)) ℂ)
    (hf0 : ∀ Q, FormalInterpolation.hasWeightedSupport v 0 (f Q))
    (hx : ∀ i, FormalInterpolation.hasWeightedSupport v R (f (x i)))
    (P : MvPolynomial (Fin (m + 1)) ℂ)
    (hP : P ∈ (Ideal.span (Set.range x)) ^ n) :
    FormalInterpolation.hasWeightedSupport v ((n : ℝ) * R) (f P) := by sorry
