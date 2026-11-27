-- Prove2me | Theorems.Thm_GRH_split_prime_lower_bound_at_squares_extends_to_mangoldt_majorant
-- name    : GRH.split_prime_lower_bound_at_squares_extends_to_mangoldt_majorant
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-27T01:44:55.50571+00:00
-- url     : https://prove2.me/theorems/19e93d16-7d0c-57bd-8092-db874381076e
-- title:
--   A lower estimate for ordinary split primes at squares controls the prime-power sum at every real cutoff
-- statement:
--   For θ≥1/2, a bound φ(q)∑log p ≥ u²−C(u²+1)^θ over primes p≤u² in class 1 gives D≥0 with D x^θ+φ(q)ψ(x;q,1)−x≥0 for every real x>1.
-- source:
--   Arithmetic reduction for GRH.centered_moebius_progression_bilinear_power_bound. The fixed-modulus equivalence is https://prove2.me/theorems/04e865ba-3dd7-43e6-9714-8e4d666e0b7c .

import Definitions.Def_GRH_SplitPrimeLower

open GRH.SplitPrimeLower

theorem GRH.split_prime_lower_bound_at_squares_extends_to_mangoldt_majorant (q : ℕ) (θ : ℝ) (hθ : (1/2:ℝ) ≤ θ) (h : squareLower q θ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x : ℝ, 1 < x → 0 ≤ primeMajorant q D θ x := by sorry
