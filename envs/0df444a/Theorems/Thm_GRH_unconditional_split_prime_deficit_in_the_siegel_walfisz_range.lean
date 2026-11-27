-- Prove2me | Theorems.Thm_GRH_unconditional_split_prime_deficit_in_the_siegel_walfisz_range
-- name    : GRH.unconditional_split_prime_deficit_in_the_siegel_walfisz_range
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-27T02:21:37.168974+00:00
-- url     : https://prove2.me/theorems/1f4fa64c-0bc3-5597-83bf-f376606e8df8
-- title:
--   Unconditional convergence of the split-prime deficit series at exponent one
-- statement:
--   For each positive modulus q the weighted positive prime deficit at square cutoffs is summable at exponent 1. A quantitative lower bound holds uniformly when q≤(log n)^A, with a deficit at most φ(q) times C n exp(−c√log n)+K√n, using constants independent of q and n for each A>0.
-- source:
--   The exact Möbius target is https://prove2.me/theorems/5000f709-1ce6-4ce6-a1ad-637c5b963006 . Its previously verified one-class reduction is https://prove2.me/submissions/413f71d4-395a-4e35-87f9-cfe99ce96800 . The prime-power estimate is the published Siegel–Walfisz theorem https://prove2.me/submissions/81593c60-fedd-42b2-9d93-584a56da2a6e .

import Definitions.Def_GRH_PrimeDeficitMean

open MeasureTheory Set Filter Topology ArithmeticFunction GRH.PrimeDeficitMean GRH.SplitPrimeLower GRH.OneSidedMoebius GRH.FactorialMoebius

theorem GRH.unconditional_split_prime_deficit_in_the_siegel_walfisz_range :
    (∀ A : ℝ, 0<A → ∃ c C K : ℝ, 0<c ∧ 0<C ∧ 0≤K ∧ ∀ (q n : ℕ), 0<q → 2≤n →
      (q:ℝ) ≤ (Real.log n)^A →
      (n:ℝ) - (q.totient:ℝ)*primeWeight q n ≤
        (q.totient:ℝ)*(C*(n:ℝ)*Real.exp (-c*Real.sqrt (Real.log n)) + K*Real.sqrt n)) ∧
    ∀ q : ℕ, [NeZero q] → squareMean q 1 := by sorry
