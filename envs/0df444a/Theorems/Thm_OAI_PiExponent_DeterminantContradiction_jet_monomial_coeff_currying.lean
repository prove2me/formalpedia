-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_jet_monomial_coeff_currying
-- name    : OAI.PiExponent.DeterminantContradiction.jet_monomial_coeff_currying
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T08:23:55.661551+00:00
-- url     : https://prove2.me/theorems/1ae6fc9a-5d3b-49fc-a072-88c0a86248de
-- title:
--   Coefficient currying for the jet monomial product
-- statement:
--   For the substituted product, extracting the coefficient indexed by `Fin.cases s b` agrees with extracting the `b` coefficient in the remaining variables and then the univariate coefficient of degree `s`. This removes the coefficient rearrangement from the parent target. It holds without positivity or nonzero assumptions, including zero exponents and zero truncation orders. A proof route is the polynomial/MvPolynomial currying equivalence with its coefficient compatibility, followed by product expansion.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent
open OAI.PiExponent.FormalInterpolation
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.jet_monomial_coeff_currying
    (m : Nat) (r : Fin m → Complex) (T : Fin m → Nat)
    (j h : Nat) (a b : Fin m → Nat) (s : Nat) :
    (MvPolynomial.coeff (InterpolationMatrix.exponentVector (Fin.cases s b))
      (∏ x : Fin (m + 1),
        (Fin.cases (1 + MvPolynomial.X 0)
          (fun i => MvPolynomial.C ((j : Complex) * r i) + MvPolynomial.X i.succ +
            Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X 0)
              (InterpolationMatrix.truncatedLog (T i))) x) ^
          (Fin.cases h a x))) =
    ((MvPolynomial.coeff (InterpolationMatrix.exponentVector b)
      (MvPolynomial.C ((1 + Polynomial.X) ^ h) *
        ∏ x : Fin m,
          (MvPolynomial.C (Polynomial.C ((j : Complex) * r x) +
              InterpolationMatrix.truncatedLog (T x)) +
            MvPolynomial.X x) ^ a x)).coeff s) := by sorry
