-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_hasWeightedSupport_of_mem_span
-- name    : OAI.PiExponent.FormalInterpolation.hasWeightedSupport_of_mem_span
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-16T05:47:52.305454+00:00
-- url     : https://prove2.me/theorems/b8351ad6-0b00-4d65-940a-ea17b01ccb3d
-- title:
--   Weighted support on a generated ideal
-- statement:
--   If a ring homomorphism sends every polynomial to a series supported in weighted degree at least zero, and sends each member of a family of generators to degree at least R, then it sends every element of the ideal they generate to degree at least R.
-- source:
--   Adapted from formalJet_mem_weighted_of_mem_pow in CompactJetPolynomial.lean, cited by the parent target.

import Definitions.Def_OAI_PiExponent_WeightedSupport
import Mathlib.RingTheory.Ideal.Operations

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem OAI.PiExponent.FormalInterpolation.hasWeightedSupport_of_mem_span
    {m : ℕ} (v : Fin (m + 1) → ℝ)
    (R : ℝ)
    (f : MvPolynomial (Fin (m + 1)) ℂ →+*
      MvPowerSeries (Fin (m + 1)) ℂ)
    (x : Fin (m + 1) → MvPolynomial (Fin (m + 1)) ℂ)
    (hf0 : ∀ Q, FormalInterpolation.hasWeightedSupport v 0 (f Q))
    (hx : ∀ i, FormalInterpolation.hasWeightedSupport v R (f (x i)))
    (Q : MvPolynomial (Fin (m + 1)) ℂ)
    (hQ : Q ∈ Ideal.span (Set.range x)) :
    FormalInterpolation.hasWeightedSupport v R (f Q) := by sorry
