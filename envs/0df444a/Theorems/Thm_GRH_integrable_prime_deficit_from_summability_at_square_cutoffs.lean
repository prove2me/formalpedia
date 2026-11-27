-- Prove2me | Theorems.Thm_GRH_integrable_prime_deficit_from_summability_at_square_cutoffs
-- name    : GRH.integrable_prime_deficit_from_summability_at_square_cutoffs
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-27T02:21:41.104504+00:00
-- url     : https://prove2.me/theorems/c2185729-a29a-5757-8573-d9cec981e2b1
-- title:
--   Weighted summability at square cutoffs controls the continuous prime deficit
-- statement:
--   For θ>1/2, convergence of the positive prime deficits at integer squares with weights u^(−2θ−1) makes the Mellin integral of the deficit against x^(−θ−1) absolutely convergent on (1,∞).
-- source:
--   The exact Möbius target is https://prove2.me/theorems/5000f709-1ce6-4ce6-a1ad-637c5b963006 . Its previously verified one-class reduction is https://prove2.me/submissions/413f71d4-395a-4e35-87f9-cfe99ce96800 .

import Definitions.Def_GRH_PrimeDeficitMean

open MeasureTheory Set Filter Topology ArithmeticFunction GRH.PrimeDeficitMean GRH.SplitPrimeLower GRH.OneSidedMoebius GRH.FactorialMoebius

theorem GRH.integrable_prime_deficit_from_summability_at_square_cutoffs (q : ℕ) (θ : ℝ) (hθ : 1/2<θ) (h : squareMean q θ) :
    IntegrableOn (fun x : ℝ => deficit q x * x^(-θ-1)) (Ioi 1) := by sorry
