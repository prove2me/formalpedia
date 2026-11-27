-- Prove2me | Theorems.Thm_GRH_centered_moebius_of_one_split_prime_class_at_factorial_squares
-- name    : GRH.centered_moebius_of_one_split_prime_class_at_factorial_squares
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-27T01:45:20.146859+00:00
-- url     : https://prove2.me/theorems/c0bfc1d1-ab01-5de0-b139-3064adce90a0
-- title:
--   The centered Möbius estimate follows from one prime residue at arbitrarily large factorial levels
-- statement:
--   At arbitrarily large k let q=(k+2)! and θ=1/2+1/(k+3). A lower estimate of exponent θ for prime log-weight in the single class 1 modulo q, at all square cutoffs, implies the all-moduli centered Möbius estimate. If the centered estimate fails, every sufficiently large k violates every proposed constant at some square.
-- source:
--   Arithmetic reduction for GRH.centered_moebius_progression_bilinear_power_bound. The fixed-modulus equivalence is https://prove2.me/theorems/04e865ba-3dd7-43e6-9714-8e4d666e0b7c . The earlier all-residue Möbius criterion is https://prove2.me/theorems/98b0a13d-fbec-40a1-99f5-f786ff91c30d .

import Definitions.Def_GRH_SplitPrimeLower

open GRH.SplitPrimeLower GRH.OneSidedMoebius GRH.FactorialMoebius

theorem GRH.centered_moebius_of_one_split_prime_class_at_factorial_squares : (cofinalPrimeLower → centeredBound) ∧
    (¬centeredBound → ∃ B : ℕ, ∀ k : ℕ, B ≤ k → ∀ C : ℝ, 0 ≤ C → ∃ u : ℕ,
      ((level k).totient:ℝ)*primeWeight (level k) (u^2) <
        (u:ℝ)^2-C*((u:ℝ)^2+1)^(exponent k)) := by sorry
