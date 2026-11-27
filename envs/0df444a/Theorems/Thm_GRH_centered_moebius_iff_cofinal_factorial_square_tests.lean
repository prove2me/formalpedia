-- Prove2me | Theorems.Thm_GRH_centered_moebius_iff_cofinal_factorial_square_tests
-- name    : GRH.centered_moebius_iff_cofinal_factorial_square_tests
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-27T00:45:27.055804+00:00
-- url     : https://prove2.me/theorems/98b0a13d-fbec-40a1-99f5-f786ff91c30d
-- title:
--   Cofinal factorial moduli and one exponent per level suffice for the full centered bound
-- statement:
--   The all-moduli centered bound is equivalent to having arbitrarily large k for which every unit class modulo (k+2)! has a raw one-sided Möbius upper bound at squares with exponent 1/2+1/(k+3). If the full bound fails, every sufficiently large level has a unit class exceeding every proposed constant at some square.
-- source:
--   The target is GRH.centered_moebius_progression_bilinear_power_bound. The earlier square-cutoff reduction and the ordinary modulus-one case are posted on Prove2Me. Induction of Dirichlet characters uses Mathlib’s LFunction_changeLevel identity.

import Definitions.Def_GRH_FactorialMoebius

open GRH.FactorialMoebius GRH.OneSidedMoebius

theorem GRH.centered_moebius_iff_cofinal_factorial_square_tests : (centeredBound ↔ diagonal) ∧
    (¬centeredBound → ∃ B : ℕ, ∀ k : ℕ, B ≤ k →
      ∃ a : ZMod (level k), IsUnit a ∧ ∀ C : ℝ, 0 ≤ C → ∃ u : ℕ,
        C * ((u:ℝ)^2+1)^(exponent k) < residue a (u^2)) := by sorry
