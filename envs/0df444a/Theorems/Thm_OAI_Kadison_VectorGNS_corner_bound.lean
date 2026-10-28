-- Prove2me | Theorems.Thm_OAI_Kadison_VectorGNS_corner_bound
-- name    : OAI.Kadison.VectorGNS.corner_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:47:00.575446+00:00
-- url     : https://prove2.me/theorems/0875db7b-39c0-41c8-8f6e-f66be3da923a
-- title:
--   OAI.Kadison.VectorGNS.corner_bound: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.VectorGNS`, with `open scoped InnerProductSpace ComplexOrder`, `open ContinuousLinearMap`, `open FreeWordTensor FreeMoments FreeWordAction FreeBlocks`):
--
--   ```lean
--   theorem corner_bound (T : H →L[ℂ] H) (ε : ℝ) (β : ℂ)
--       (hbound : ∀ q : D,IsStarProjection (f q) → subalgebraTrace M ξ (f q)=β →
--         ∀ a : M,f q*a=a → a*f q=a →
--           ‖T*(a:H →L[ℂ] H)-(a:H →L[ℂ] H)*T‖≤ε*‖a‖)
--       (X : (subalgebraTrace M ξ).GNS →L[ℂ] (subalgebraTrace M ξ).GNS)
--       (hX : CornerSymmetrization.CornerElement
--         (factorOperators (vectorState M ξ hfaith hone) f)
--         (ambientOperators (vectorState M ξ hfaith hone) R)
--         (TracialGNS.vacuum (subalgebraTrace M ξ)) β X) :
--       ‖compression (subalgebraTrace M ξ) M.toStarSubalgebra.subtype ξ (subalgebraTrace_subtype M ξ) T*X-
--         X*compression (subalgebraTrace M ξ) M.toStarSubalgebra.subtype ξ (subalgebraTrace_subtype M ξ) T‖≤ε*‖X‖
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.TracialGNS.vacuum` and `OAI.Kadison.VonNeumannCStar.starOrderedRing` (definitions bundle `OAIQ039C003` of this split); `OAI.Kadison.CornerSymmetrization.CornerElement` (definitions bundle `OAIQ039C004` of this split); `OAI.Kadison.FreeWordTensor.FaithfulState` (definitions bundle `OAIQ039C010` of this split); `OAI.Kadison.VonNeumannCStar.cstarAlgebra` (definitions bundle `OAIQ039C022` of this split); `OAI.Kadison.VectorGNS.subalgebraTrace` (definitions bundle `OAIQ039C037` of this split); `OAI.Kadison.VectorGNS.compression` (definitions bundle `OAIQ039C041` of this split); `OAI.Kadison.VectorGNS.subalgebraTrace_subtype` (definitions bundle `OAIQ039C052` of this split); `OAI.Kadison.FreeBlocks.ambientOperators` and `OAI.Kadison.FreeBlocks.factorOperators` (definitions bundle `OAIQ039C055` of this split); `OAI.Kadison.VectorGNS.vectorState` (definitions bundle `OAIQ039C065` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.VectorGNS.free_original_bound_represented` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C065

section

attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped InnerProductSpace ComplexOrder

open ContinuousLinearMap

namespace Kadison.VectorGNS

open FreeWordTensor FreeMoments FreeWordAction FreeBlocks

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (ξ : H)

variable (htr : ∀ a b : M,subalgebraTrace M ξ (a*b)=subalgebraTrace M ξ (b*a))
  (hfaith : ∀ a : M,subalgebraTrace M ξ (star a*a)=0 → a=0)
  (hone : subalgebraTrace M ξ 1=1)

variable {D : Type} [CStarAlgebra D] (f : D →⋆ₐ[ℂ] M)
  (R : Bool → StarSubalgebra ℂ M)

include htr in
theorem corner_bound (T : H →L[ℂ] H) (ε : ℝ) (β : ℂ)
    (hbound : ∀ q : D,IsStarProjection (f q) → subalgebraTrace M ξ (f q)=β →
      ∀ a : M,f q*a=a → a*f q=a →
        ‖T*(a:H →L[ℂ] H)-(a:H →L[ℂ] H)*T‖≤ε*‖a‖)
    (X : (subalgebraTrace M ξ).GNS →L[ℂ] (subalgebraTrace M ξ).GNS)
    (hX : CornerSymmetrization.CornerElement
      (factorOperators (vectorState M ξ hfaith hone) f)
      (ambientOperators (vectorState M ξ hfaith hone) R)
      (TracialGNS.vacuum (subalgebraTrace M ξ)) β X) :
    ‖compression (subalgebraTrace M ξ) M.toStarSubalgebra.subtype ξ (subalgebraTrace_subtype M ξ) T*X-
      X*compression (subalgebraTrace M ξ) M.toStarSubalgebra.subtype ξ (subalgebraTrace_subtype M ξ) T‖≤ε*‖X‖ := by
  sorry

end Kadison.VectorGNS

end

end
end

end OAI
end
