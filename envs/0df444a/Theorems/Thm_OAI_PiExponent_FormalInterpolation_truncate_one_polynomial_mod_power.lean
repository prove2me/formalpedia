-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncate_one_polynomial_mod_power
-- name    : OAI.PiExponent.FormalInterpolation.truncate_one_polynomial_mod_power
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T09:07:32.674986+00:00
-- url     : https://prove2.me/theorems/6e1aae79-0d0e-429b-8649-b4327b6c1511
-- title:
--   Truncate one generator polynomial modulo an ideal power
-- statement:
--   Deleting from F all monomials whose total degree times s is at least n leaves G with the strict cutoff, while the deleted part evaluates into I^n. A proof route is to expand F as a finite sum of monomials, show each deleted monomial evaluates into I^n using hg and ideal-power monotonicity, then sum those terms.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.truncate_one_polynomial_mod_power
    {d m : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (s n : Nat) (hs : 0 < s) (hn : 0 < n)
    (g : Fin m → MvPolynomial (Fin d) Complex)
    (hg : ∀ j, g j ∈ I ^ s)
    (F : MvPolynomial (Fin m) Complex) :
    ∃ G : MvPolynomial (Fin m) Complex,
      (∀ u ∈ G.support, s * (∑ j, u j) < n) ∧
      MvPolynomial.aeval g (F - G) ∈ I ^ n := by sorry
