-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_eventual_logarithmic_word_rigidity
-- name    : OAI.PiExponent.FormalInterpolation.eventual_logarithmic_word_rigidity
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-21T03:42:32.954618+00:00
-- url     : https://prove2.me/theorems/e2706cde-6ce5-49ef-9155-e1f9acf405b5
-- title:
--   Persistent logarithmic derivative vanishing forces a constant zeroth coordinate
-- statement:
--   Under the separated-product inequalities, at sufficiently large heights a nonzero bounded-weight polynomial whose logarithmic words through cost sigma N all vanish on the curve forces its zeroth coordinate to be constant. This is independent of the centers, contact, and volume assumptions.

import Definitions.Def_OAI_PiExponent_LogarithmicWordContact
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.eventual_logarithmic_word_rigidity
    {m : Nat} (hm : 1 ≤ m) (w v : Fin (m + 1) → Rat) (sigma : Rat)
    (hsigma : 0 < (sigma : Real))
    (hw : ∀ i, 0 < (w i : Real)) (hv : ∀ i, 0 < (v i : Real))
    (hseparated : ∀ A B : Finset (Fin (m + 1)), A.card = B.card →
      ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
        (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
        interpolationSeparationConstant m sigma *
          (∏ j ∈ B, (v j : Real)) < ∏ j ∈ A, (w j : Real))
    (E : Type) [Field E] [Algebra Complex E] [Algebra.EssFiniteType Complex E]
    (htrdeg : Algebra.trdeg Complex E = 1) (x : Fin (m + 1) → E)
    (hgen : IntermediateField.adjoin Complex (Set.range x) = ⊤) :
    ∃ N₀ : Nat, ∀ N : Nat, N₀ ≤ N → 0 < N →
      ∀ F : MvPolynomial (Fin (m + 1)) Complex, F ≠ 0 →
        logarithmicDegreeBound w (N : Real) F →
        (∀ word : List (Fin (m + 1)),
          logarithmicFrameCost v word ≤ (sigma : Real) * (N : Real) →
          MvPolynomial.aeval x (logarithmicFrameWord word F) = 0) →
        ∃ a : Complex, x 0 = algebraMap Complex E a := by sorry
