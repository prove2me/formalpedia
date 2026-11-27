-- Prove2me | Theorems.Thm_GRH_prime_square_fourier_filter_and_coprime_harmonic_recursion
-- name    : GRH.prime_square_fourier_filter_and_coprime_harmonic_recursion
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-27T06:03:43.53882+00:00
-- url     : https://prove2.me/theorems/c5b28f76-bf4a-476d-afcc-404fae3208d5
-- title:
--   An exact prime-square Fourier filter and a coprime harmonic recurrence
-- statement:
--   For each prime p, p S_N(x) plus the sum of S_N(x+j/p²) over j modulo p² coprime to p, plus the sum of S_{pN}(x/p+j/p) over all j modulo p, vanishes. Also H_p(U)=H_1(U)+H_p(⌊U/p⌋)/p.
-- source:
--   For the Möbius function, write S_N(x) for the sum of μ(n) exp(2πinx) through N. The bilinear sum B(q,a,N) and the coprime reciprocal sum H_q(U) use the original mission normalizations. The decomposition uses Mathlib’s primitive additive character on ZMod and the squarefree support and multiplicativity of μ.

import Definitions.Def_GRH_SquarefullFrequencies

open Finset GRH.AdditiveMoebiusSpectrum GRH.SquarefullFrequencies

theorem GRH.prime_square_fourier_filter_and_coprime_harmonic_recursion (p : ℕ) [NeZero p] (hp : p.Prime) :
    (∀ (N : ℕ) (x : ℚ), (p : ℂ)*transform false N x + primeSquareShifts p N x +
      shifts p (p*N) (x/p) = 0) ∧
    (∀ U : ℕ, GRH.reducedMoebiusHarmonic p U = GRH.reducedMoebiusHarmonic 1 U +
      GRH.reducedMoebiusHarmonic p (U/p)/(p : ℝ)) := by sorry
