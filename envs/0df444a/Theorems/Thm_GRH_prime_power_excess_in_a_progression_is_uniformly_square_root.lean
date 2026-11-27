-- Prove2me | Theorems.Thm_GRH_prime_power_excess_in_a_progression_is_uniformly_square_root
-- name    : GRH.prime_power_excess_in_a_progression_is_uniformly_square_root
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-27T02:21:47.529937+00:00
-- url     : https://prove2.me/theorems/3d79c0a3-a0b3-47b5-bf14-61dc9f530d0f
-- title:
--   A uniform square-root bound for the prime-power excess in residue 1
-- statement:
--   For every modulus and every integer cutoff n, the von Mangoldt sum in residue 1 exceeds the ordinary prime log-weight by a nonnegative amount at most K√n, for one absolute K≥0.
-- source:
--   The exact Möbius target is https://prove2.me/theorems/5000f709-1ce6-4ce6-a1ad-637c5b963006 . Its previously verified one-class reduction is https://prove2.me/submissions/413f71d4-395a-4e35-87f9-cfe99ce96800 .

import Definitions.Def_GRH_PrimeDeficitMean

open MeasureTheory Set Filter Topology ArithmeticFunction GRH.PrimeDeficitMean GRH.SplitPrimeLower GRH.OneSidedMoebius GRH.FactorialMoebius

theorem GRH.prime_power_excess_in_a_progression_is_uniformly_square_root : ∃ K : ℝ, 0 ≤ K ∧ ∀ q n : ℕ,
    0 ≤ mangoldtWeight q n - primeWeight q n ∧
    mangoldtWeight q n - primeWeight q n ≤ K * Real.sqrt n := by sorry
