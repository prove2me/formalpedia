-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncatedPolynomialJet_glue_of_separating_coordinate_selectors
-- name    : OAI.PiExponent.FormalInterpolation.truncatedPolynomialJet_glue_of_separating_coordinate_selectors
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T22:17:16.446042+00:00
-- url     : https://prove2.me/theorems/83a00444-1e1d-49a8-87b7-907ba12990b0
-- title:
--   Gluing prescribed jets from local selectors
-- statement:
--   Given selectors with the stated box-coefficient behavior, combine them with the prescribed polynomials to obtain one polynomial matching every requested truncated jet coefficient. Use the finite sum of selector-polynomial products and the coefficient convolution formula; selector coefficients outside the box are irrelevant because every contributing exponent is bounded coordinatewise by the target exponent.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.RingTheory.Ideal.Quotient.Operations

open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.truncatedPolynomialJet_glue_of_separating_coordinate_selectors
    {m : Nat} (K : Nat) (T : Fin m → Nat)
    (c : Fin K → Fin m → Complex)
    (S : Fin (m + 1) → Nat)
    (Q : Fin K → MvPolynomial (Fin (m + 1)) Complex)
    (E : Fin K → MvPolynomial (Fin (m + 1)) Complex)
    (hsel : ∀ (j k : Fin K)
      (a : {a : Fin (m + 1) → Nat // ∀ i, a i < S i}),
      (truncatedPolynomialJet (c j) T (E k)).coeff
          (InterpolationMatrix.exponentVector a.1) =
        if j = k ∧ a.1 = 0 then 1 else 0) :
    ∃ P : MvPolynomial (Fin (m + 1)) Complex,
      ∀ (j : Fin K)
        (a : {a : Fin (m + 1) → Nat // ∀ i, a i < S i}),
        (truncatedPolynomialJet (c j) T P).coeff
            (InterpolationMatrix.exponentVector a.1) =
          (truncatedPolynomialJet (c j) T (Q j)).coeff
            (InterpolationMatrix.exponentVector a.1) := by sorry
