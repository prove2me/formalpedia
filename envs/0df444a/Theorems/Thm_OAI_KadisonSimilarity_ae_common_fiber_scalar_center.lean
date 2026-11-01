-- Prove2me | Theorems.Thm_OAI_KadisonSimilarity_ae_common_fiber_scalar_center
-- name    : OAI.KadisonSimilarity.ae_common_fiber_scalar_center
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T09:09:39.513997+00:00
-- url     : https://prove2.me/theorems/97288eb0-abfe-4a9f-8743-89e812423fac
-- title:
--   OAI.KadisonSimilarity.ae_common_fiber_scalar_center: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KadisonSimilarity.similarityTheorem`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KadisonSimilarity.ae_common_fiber_scalar_center` of [lean/OAI/Analysis/KadisonSimilarity/Representation/CommonFiberFactors.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/Representation/CommonFiberFactors.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KadisonSimilarity`, with `open MeasureTheory Filter`):
--
--   ```lean
--   theorem ae_common_fiber_scalar_center
--       (B C : StarSubalgebra ℂ (H →L[ℂ] H))
--       [IsClosed (B : Set (H →L[ℂ] H))] [IsClosed (C : Set (H →L[ℂ] H))]
--       (hBC : ∀ b : B, ∀ c : C, (b : H →L[ℂ] H) * (c : H →L[ℂ] H) =
--         (c : H →L[ℂ] H) * (b : H →L[ℂ] H))
--       (hgen : representationVonNeumannAlgebra (jointCStarSource B C).subtype =
--         starSubalgebraCommutant π.range)
--       (s : Set (WeakDual.characterSpace ℂ A)) (hs : MeasurableSet s)
--       (hnull : (cyclicCommonBaseMeasure π D) sᶜ = 0)
--       (ρ : ∀ _x : s, Unitization ℂ (jointCStarSource B C) →⋆ₐ[ℂ]
--         (ScalarHilbertCoordinates D.generators →L[ℂ] ScalarHilbertCoordinates D.generators))
--       (hρ : ∀ b : jointCStarSource B C, ∀ f : CommonCyclicHilbert π D,
--         ∀ᵐ x : s ∂Measure.comap ((↑) : s → WeakDual.characterSpace ℂ A)
--           (cyclicCommonBaseMeasure π D),
--           isometricExtension (cyclicCommonEmbedding π D) (b : H →L[ℂ] H) f x =
--             ρ x (Unitization.inr b) (f x)) :
--       ∀ᵐ x ∂cyclicCommonBaseMeasure π D,
--         commonFirstFiberScalarCenter π D B C s ρ x
--   ```
--
--   **Definitions.** The statement is written with `OAI.KadisonSimilarity.ScalarHilbertCoordinates`, `OAI.KadisonSimilarity.commonCyclicMeasurable`, `OAI.KadisonSimilarity.isometricExtension`, `OAI.KadisonSimilarity.representationVonNeumannAlgebra` and `OAI.KadisonSimilarity.starSubalgebraCommutant` (definitions bundle `OAIQ075A005` of this split); `OAI.KadisonSimilarity.jointCStarSource` and `OAI.KadisonSimilarity.jointCStarSource_isClosed` (definitions bundle `OAIQ075A006` of this split); `OAI.KadisonSimilarity.CommonCyclicHilbert`, `OAI.KadisonSimilarity.CyclicDecompositionData` and `OAI.KadisonSimilarity.cyclicCommonBaseMeasure` (definitions bundle `OAIQ075A010` of this split); `OAI.KadisonSimilarity.cyclicCommonEmbedding` (definitions bundle `OAIQ075A017` of this split); `OAI.KadisonSimilarity.commonFirstFiberScalarCenter` (definitions bundle `OAIQ075A029` of this split).
--
--   **Used by.** The proof of `OAI.KadisonSimilarity.publishedUniformInputs` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/Representation/CommonFiberFactors.lean (declaration OAI.KadisonSimilarity.ae_common_fiber_scalar_center)

import Mathlib
import Definitions.Def_OAIQ075A029

section

attribute [-instance] _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace KadisonSimilarity
open MeasureTheory Filter

universe u
variable {A H : Type u} [CommCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (D : CyclicDecompositionData π.range)

attribute [local instance] commonCyclicMeasurable commonCyclicBorel commonCyclicCountable

theorem ae_common_fiber_scalar_center
    (B C : StarSubalgebra ℂ (H →L[ℂ] H))
    [IsClosed (B : Set (H →L[ℂ] H))] [IsClosed (C : Set (H →L[ℂ] H))]
    (hBC : ∀ b : B, ∀ c : C, (b : H →L[ℂ] H) * (c : H →L[ℂ] H) =
      (c : H →L[ℂ] H) * (b : H →L[ℂ] H))
    (hgen : representationVonNeumannAlgebra (jointCStarSource B C).subtype =
      starSubalgebraCommutant π.range)
    (s : Set (WeakDual.characterSpace ℂ A)) (hs : MeasurableSet s)
    (hnull : (cyclicCommonBaseMeasure π D) sᶜ = 0)
    (ρ : ∀ _x : s, Unitization ℂ (jointCStarSource B C) →⋆ₐ[ℂ]
      (ScalarHilbertCoordinates D.generators →L[ℂ] ScalarHilbertCoordinates D.generators))
    (hρ : ∀ b : jointCStarSource B C, ∀ f : CommonCyclicHilbert π D,
      ∀ᵐ x : s ∂Measure.comap ((↑) : s → WeakDual.characterSpace ℂ A)
        (cyclicCommonBaseMeasure π D),
        isometricExtension (cyclicCommonEmbedding π D) (b : H →L[ℂ] H) f x =
          ρ x (Unitization.inr b) (f x)) :
    ∀ᵐ x ∂cyclicCommonBaseMeasure π D,
      commonFirstFiberScalarCenter π D B C s ρ x := by
  sorry

end KadisonSimilarity

end

end OAI
end
