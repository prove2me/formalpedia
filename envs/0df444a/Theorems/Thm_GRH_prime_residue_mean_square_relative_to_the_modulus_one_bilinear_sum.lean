-- Prove2me | Theorems.Thm_GRH_prime_residue_mean_square_relative_to_the_modulus_one_bilinear_sum
-- name    : GRH.prime_residue_mean_square_relative_to_the_modulus_one_bilinear_sum
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-27T06:03:53.497031+00:00
-- url     : https://prove2.me/theorems/35ede6c1-bad7-4f7f-9285-88a906723886
-- title:
--   A dyadic prime mean square relative to the ordinary bilinear sum
-- statement:
--   Write V_p for the sum over all residues of (B(p,a,N)−B(1,0,N)/p)² and W_p for the variance about the prime row’s own mean. Then pV_p=pW_p+[N(H_1(⌊√N⌋)²−H_p(⌊√N⌋)²)]². On every set of primes Q<p≤2Q with integer Q≥1, the sum of pV_p is bounded by (4Q²+13(N+1))N+4N²/Q. The same right side bounds Q times T² times the number of residue classes whose absolute deviation exceeds T≥0.
-- source:
--   For the Möbius function, write S_N(x) for the sum of μ(n) exp(2πinx) through N. The bilinear sum B(q,a,N) and the coprime reciprocal sum H_q(U) use the original mission normalizations. Public inputs are the signed residue identity https://prove2.me/submissions/dc0048dc-5648-4712-8b8c-07d527bc5d09 , the prime mean-square large sieve https://prove2.me/submissions/365f47be-8496-474e-89c4-fe5124c4b0cc and Helfgott’s coprime reciprocal bound https://prove2.me/submissions/e110685c-05e3-418b-9139-db1604ac9ee5 .

import Definitions.Def_GRH_SquarefullFrequencies

open Finset GRH.AdditiveMoebiusSpectrum GRH.SquarefullFrequencies

theorem GRH.prime_residue_mean_square_relative_to_the_modulus_one_bilinear_sum :
    (∀ (p : Nat.Primes) (N : ℕ), (p.val : ℝ)*relativeVariance p N = (p.val : ℝ)*primeVariance p N +
      ((N : ℝ)*((GRH.reducedMoebiusHarmonic 1 N.sqrt)^2-
        (primeHarmonic p N.sqrt)^2))^2) ∧
    (∀ (Q N : ℕ), 0 < Q → ∀ P : Finset Nat.Primes, (∀ p ∈ P, Q < p.val ∧ p.val ≤ 2*Q) →
      (∑ p ∈ P, (p.val : ℝ)*relativeVariance p N) ≤ (4*(Q : ℝ)^2+13*((N : ℝ)+1))*N+4*(N : ℝ)^2/Q ∧
      ∀ T : ℝ, 0 ≤ T → (Q : ℝ)*T^2*(∑ p ∈ P, (exceptionalResidues p N T : ℝ)) ≤
        (4*(Q : ℝ)^2+13*((N : ℝ)+1))*N+4*(N : ℝ)^2/Q) := by sorry
