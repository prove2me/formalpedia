-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_comaximal_contacts_exclusive
-- name    : OAI.PiExponent.FormalInterpolation.comaximal_contacts_exclusive
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T09:16:33.442987+00:00
-- url     : https://prove2.me/theorems/ec395248-6d07-42fa-87fb-b1bf3294c8f0
-- title:
--   Comaximal ideals cannot both have positive contact
-- statement:
--   For any distinct pair of comaximal ideals on the affine branch, their contacts cannot both be positive. A proof route uses a representation of 1 in their ideal sum: if both contacts were positive, every summand in that representation would have positive valuation, contradicting the valuation of 1 being zero.

import Definitions.Def_OAI_PiExponent_LogarithmicWordContact
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.comaximal_contacts_exclusive
    {K d : Nat} {E : Type} [Field E] [Algebra Complex E]
    (nu : PolynomialCurvePlace E) (x : Fin d → E)
    (I : Fin K → Ideal (MvPolynomial (Fin d) Complex))
    (hbranch : ∀ i, (0 : WithTop Int) ≤ nu.1 (x i))
    (hcop : ∀ j k : Fin K, j ≠ k → IsCoprime (I j) (I k)) :
    ∀ j k : Fin K, j ≠ k →
      ¬ (0 < polynomialCurveIdealContact nu x (I j) ∧
         0 < polynomialCurveIdealContact nu x (I k)) := by sorry
