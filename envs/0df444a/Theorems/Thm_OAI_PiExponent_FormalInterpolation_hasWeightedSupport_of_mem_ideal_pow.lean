-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_hasWeightedSupport_of_mem_ideal_pow
-- name    : OAI.PiExponent.FormalInterpolation.hasWeightedSupport_of_mem_ideal_pow
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T05:48:06.535278+00:00
-- url     : https://prove2.me/theorems/7dd2349f-a421-4b49-a732-0c0aa1fad2a8
-- title:
--   Weighted support of powers of a supported ideal
-- statement:
--   If all polynomial images have weighted support at least zero and all elements of an ideal have weighted support at least R, then the image of every element in the nth power of that ideal has weighted support at least nR, including the zeroth power.
-- source:
--   Adapted from formalJet_mem_weighted_of_mem_pow in CompactJetPolynomial.lean, cited by the parent target.

import Definitions.Def_OAI_PiExponent_WeightedSupport
import Mathlib.RingTheory.Ideal.Operations

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem OAI.PiExponent.FormalInterpolation.hasWeightedSupport_of_mem_ideal_pow
    {m : ℕ} (v : Fin (m + 1) → ℝ)
    (R : ℝ) (n : ℕ)
    (f : MvPolynomial (Fin (m + 1)) ℂ →+*
      MvPowerSeries (Fin (m + 1)) ℂ)
    (I : Ideal (MvPolynomial (Fin (m + 1)) ℂ))
    (hf0 : ∀ Q, FormalInterpolation.hasWeightedSupport v 0 (f Q))
    (hI : ∀ Q, Q ∈ I → FormalInterpolation.hasWeightedSupport v R (f Q))
    (P : MvPolynomial (Fin (m + 1)) ℂ)
    (hP : P ∈ I ^ n) :
    FormalInterpolation.hasWeightedSupport v ((n : ℝ) * R) (f P) := by sorry
