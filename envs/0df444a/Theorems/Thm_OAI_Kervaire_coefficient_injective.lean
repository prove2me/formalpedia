-- Prove2me | Theorems.Thm_OAI_Kervaire_coefficient_injective
-- name    : OAI.Kervaire.coefficient_injective
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:51.507274+00:00
-- url     : https://prove2.me/theorems/5ce01a8c-d930-48fb-8b8d-97e2f037a12e
-- statement:
--   The theorem states that, for any group A and any element w of the free product A * ℤ (written multiplicatively, the coproduct of A with the infinite cyclic group Multiplicative ℤ), if w is unimodular, meaning that its exponent sum, the integer obtained by projecting w onto the ℤ factor, equals 1 or -1, then the natural map from A into the quotient of A * ℤ by the normal closure of w is injective. That map sends a to the class of its image under the left inclusion of A into the free product. Equivalently, A embeds in the group obtained from A by adjoining one new generator t and imposing the single relation w = 1, whenever the exponent sum of t in w is ±1. The statement is admitted in the source, not proved there.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/Kervaire.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/Kervaire.lean; bytes 945..1093
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_Kervaire

namespace OAI

noncomputable section

namespace Kervaire

universe u

theorem coefficient_injective (A : Type u) [Group A] (w : WordGroup A)
    (hw : Unimodular w) : Function.Injective (coefficientMap w) := by
  sorry

end Kervaire
end
end OAI
