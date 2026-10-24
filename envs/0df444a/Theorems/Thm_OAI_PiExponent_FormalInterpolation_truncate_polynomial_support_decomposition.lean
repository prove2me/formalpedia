-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncate_polynomial_support_decomposition
-- name    : OAI.PiExponent.FormalInterpolation.truncate_polynomial_support_decomposition
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T09:17:10.695875+00:00
-- url     : https://prove2.me/theorems/81e999e6-3294-48fd-8f89-8cf49b50907d
-- title:
--   Decompose a polynomial at a strict total-degree cutoff
-- statement:
--   Filter the finitely supported coefficients of F to retain precisely the exponents whose total degree times s is strictly below n. The difference F − G is the finite sum of the complementary monomials.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.truncate_polynomial_support_decomposition
    {m : Nat} (s n : Nat) (F : MvPolynomial (Fin m) Complex) :
    ∃ G : MvPolynomial (Fin m) Complex,
      (∀ u ∈ G.support, s * (∑ j : Fin m, u j) < n) ∧
      F - G =
        ∑ u ∈ F.support.filter (fun u => ¬ s * (∑ j : Fin m, u j) < n),
          MvPolynomial.monomial u (F.coeff u) := by sorry
