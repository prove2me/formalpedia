-- Prove2me | Theorems.Thm_GRH_moebius_large_sieve_energy_and_exceptional_farey_count
-- name    : GRH.moebius_large_sieve_energy_and_exceptional_farey_count
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-27T05:16:06.824194+00:00
-- url     : https://prove2.me/theorems/8f030f31-3852-4159-b896-64c698ec86f8
-- title:
--   A large-sieve bound for exceptional Möbius frequencies and prime-modulus row variance
-- statement:
--   For distinct rational frequencies in [0,1) with denominator at most Q≥2, both Möbius transforms have total squared magnitude at most (Q²+13(N+1))N. The number above amplitude T, multiplied by T², obeys the same bound. Summing p times the squared residue deviations of the actual centered bilinear row over any collection of primes p≤Q also obeys that bound.
-- source:
--   Möbius bilinear progression problem on Prove2Me. The finite sums and all normalizations use the original GRH_MoebiusBilinear definition. The Fourier character is Mathlib’s ZMod.stdAddChar. Additive large sieve https://prove2.me/theorems/05ab9246-ae34-437e-b76b-44598dd6c900 .

import Definitions.Def_GRH_AdditiveMoebiusSpectrum

open Finset GRH.AdditiveMoebiusSpectrum

theorem GRH.moebius_large_sieve_energy_and_exceptional_farey_count (Q N : ℕ) (hQ : 2 ≤ Q) :
    (∀ (s : Bool) (A : Finset ℚ), (∀ x ∈ A, 0 ≤ x ∧ x < 1 ∧ x.den ≤ Q) →
      (∑ x ∈ A, ‖transform s N x‖^2) ≤ ((Q : ℝ)^2+13*((N : ℝ)+1))*N ∧
      (∀ T : ℝ, 0 ≤ T → ((exceptional s N A T).card : ℝ)*T^2 ≤
        ((Q : ℝ)^2+13*((N : ℝ)+1))*N)) ∧
    (∀ P : Finset Nat.Primes, (∀ p ∈ P, p.val ≤ Q) →
      (∑ p ∈ P, (p.val : ℝ)*primeVariance p N) ≤ ((Q : ℝ)^2+13*((N : ℝ)+1))*N) := by sorry
