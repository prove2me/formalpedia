-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_pairwise_comaximal_positive_contact_exclusive
-- name    : OAI.PiExponent.FormalInterpolation.pairwise_comaximal_positive_contact_exclusive
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T09:26:45.609148+00:00
-- url     : https://prove2.me/theorems/3d8ae67e-404d-4f15-adbb-814cf9a8301c
-- title:
--   Pairwise comaximal ideals cannot both have positive contact
-- statement:
--   On the affine branch, distinct pairwise comaximal ideals cannot both have positive contact. This removes the uniqueness-of-positive-factor argument from the parent. For each distinct pair, use comaximality to write 1 as a sum of an element from each ideal. Nonnegative coordinate valuations imply evaluated polynomials have nonnegative valuation; positive contact forces both summands to have positive valuation, contradicting that the valuation of 1 is zero.

import Definitions.Def_OAI_PiExponent_LogarithmicWordContact
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.pairwise_comaximal_positive_contact_exclusive
    {K d : Nat} {E : Type} [Field E] [Algebra Complex E]
    (nu : PolynomialCurvePlace E) (x : Fin d → E)
    (I : Fin K → Ideal (MvPolynomial (Fin d) Complex))
    (hbranch : ∀ i, (0 : WithTop Int) ≤ nu.1 (x i))
    (hcop : ∀ j k : Fin K, j ≠ k → IsCoprime (I j) (I k)) :
    ∀ j k : Fin K, j ≠ k →
      ¬ (0 < polynomialCurveIdealContact nu x (I j) ∧
         0 < polynomialCurveIdealContact nu x (I k)) := by sorry
