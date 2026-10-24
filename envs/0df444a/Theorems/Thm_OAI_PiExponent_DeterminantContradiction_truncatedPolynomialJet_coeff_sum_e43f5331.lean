-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_truncatedPolynomialJet_coeff_sum_e43f5331
-- name    : OAI.PiExponent.DeterminantContradiction.truncatedPolynomialJet_coeff_sum_e43f5331
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T08:05:38.648911+00:00
-- url     : https://prove2.me/theorems/1cc5d1ac-263f-49c8-80e8-0519d5c9d731
-- title:
--   Jet coefficient extraction preserves finite sums
-- statement:
--   For a finite family of multivariate polynomials, applying the truncated jet and extracting a fixed coefficient gives the sum of the extracted coefficients of the individually mapped polynomials.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent.FormalInterpolation
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.truncatedPolynomialJet_coeff_sum_e43f5331
    {α : Type*} [Fintype α] (m : Nat)
    (c : Fin m → Complex) (T : Fin m → Nat)
    (e : Fin (m + 1) →₀ Nat)
    (f : α → MvPolynomial (Fin (m + 1)) Complex) :
    (truncatedPolynomialJet c T (∑ x, f x)).coeff e =
      ∑ x, (truncatedPolynomialJet c T (f x)).coeff e := by sorry
