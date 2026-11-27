-- Prove2me | Theorems.Thm_GRH_failure_of_centered_bound_forces_a_recurrent_fixed_rational_frequency
-- name    : GRH.failure_of_centered_bound_forces_a_recurrent_fixed_rational_frequency
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-27T05:15:51.841721+00:00
-- url     : https://prove2.me/theorems/5b2fd482-ded6-4462-b479-ed8fc9bf981c
-- title:
--   Failure of the centered Möbius bound forces one rational frequency to recur
-- statement:
--   If each fixed rational frequency in [0,1) eventually stays below (u²+1)^θ at square cutoffs for every 1/2<θ<1, the original centered bound holds for every residue. A failure of the original bound produces one fixed rational point and one fixed exponent that reappear at arbitrarily large square cutoffs in exceptional Farey sets of size at most 18u^(4−4θ) for u≥2.
-- source:
--   Möbius bilinear progression problem on Prove2Me. The finite sums and all normalizations use the original GRH_MoebiusBilinear definition. The Fourier character is Mathlib’s ZMod.stdAddChar. Square residual equivalence https://prove2.me/theorems/b1cc026b-b5ab-5744-b1e2-eaee7b654e01 and reduced reciprocal transfer https://prove2.me/theorems/d5ab2d09-0f56-4b08-b160-bf32085f60bc .

import Definitions.Def_GRH_AdditiveMoebiusSpectrum

open Finset GRH.AdditiveMoebiusSpectrum

theorem GRH.failure_of_centered_bound_forces_a_recurrent_fixed_rational_frequency :
    (escapes → ∀ (q : ℕ) [NeZero q] (a : ZMod q) (σ : ℝ), 1/2 < σ → σ < 1 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
        |GRH.centeredMoebiusBilinear q a N| ≤ C*((N : ℝ)+1)^σ) ∧
    (∀ (θ : ℝ), 0 ≤ θ → ∀ u : ℕ, 2 ≤ u →
      ((exceptional false (u^2) (fareySet u) (((u : ℝ)^2+1)^θ)).card : ℝ) ≤
        18*(u : ℝ)^(4-4*θ)) ∧
    (¬ GRH.OneSidedMoebius.centeredBound → ∃ x : ℚ, 0 ≤ x ∧ x < 1 ∧
      ∃ θ : ℝ, 1/2 < θ ∧ θ < 1 ∧ ∀ U : ℕ, ∃ u : ℕ, U ≤ u ∧
        x ∈ exceptional false (u^2) (fareySet u) (((u : ℝ)^2+1)^θ)) := by sorry
