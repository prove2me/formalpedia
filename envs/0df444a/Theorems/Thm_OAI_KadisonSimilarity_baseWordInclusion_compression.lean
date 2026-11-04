-- Prove2me | Theorems.Thm_OAI_KadisonSimilarity_baseWordInclusion_compression
-- name    : OAI.KadisonSimilarity.baseWordInclusion_compression
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-03T17:17:10.735568+00:00
-- url     : https://prove2.me/theorems/8b10e9b6-e4fd-4386-b240-0be6e7f32ddc
-- title:
--   OAI.KadisonSimilarity.baseWordInclusion_compression: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KadisonSimilarity.similarityTheorem`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KadisonSimilarity.baseWordInclusion_compression` of [lean/OAI/Analysis/KadisonSimilarity/FreeProduct/WordBaseCoordinates.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/FreeProduct/WordBaseCoordinates.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KadisonSimilarity`):
--
--   ```lean
--   theorem baseWordInclusion_compression (Y : H →L[ℂ] H)
--       (T : WordMultiplicity ΩA 0 →L[ℂ] WordMultiplicity ΩA 0)
--       (hY : ∀ v, Y (U.inclusion 0 (hilbertTensorInsert v (emptyEndpoint (F := F) ΩD))) =
--         U.inclusion 0 (hilbertTensorInsert (T v) (emptyEndpoint (F := F) ΩD))) :
--       (baseWordInclusion ΩA U ΩD hΩD).toContinuousLinearMap.adjoint.comp
--         (Y.comp (baseWordInclusion ΩA U ΩD hΩD).toContinuousLinearMap) =
--           zeroMultiplicityOperator ΩA T
--   ```
--
--   **Definitions.** The statement is written with `OAI.KadisonSimilarity.CompletedTensorWord`, `OAI.KadisonSimilarity.HilbertTensor`, `OAI.KadisonSimilarity.OrthogonalWordLevels`, `OAI.KadisonSimilarity.TensorWord`, `OAI.KadisonSimilarity.centeredSubspace`, `OAI.KadisonSimilarity.hilbertTensorInnerProductSpace`, `OAI.KadisonSimilarity.hilbertTensorNormedAddCommGroup`, `OAI.KadisonSimilarity.tensorWordSpace` and `OAI.KadisonSimilarity.TensorWordSpace` (definitions bundle `OAIQ075A004` of this split); `OAI.KadisonSimilarity.EndpointTensor` (definitions bundle `OAIQ075A009` of this split); `OAI.KadisonSimilarity.MultiplicityWordSpace`, `OAI.KadisonSimilarity.WordMultiplicity`, `OAI.KadisonSimilarity.baseWordInclusion`, `OAI.KadisonSimilarity.emptyEndpoint`, `OAI.KadisonSimilarity.hilbertTensorInsert` and `OAI.KadisonSimilarity.zeroMultiplicityOperator` (definitions bundle `OAIQ075A016` of this split).
--
--   **Used by.** The proof of `OAI.KadisonSimilarity.TracialCornerGeometry.free_corner_estimate_of_published_words` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/FreeProduct/WordBaseCoordinates.lean (declaration OAI.KadisonSimilarity.baseWordInclusion_compression)

import Mathlib
import Definitions.Def_OAIQ075A016

section

attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace KadisonSimilarity

universe u
variable {E F : Type u} {B H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ΩA : B)
  (U : OrthogonalWordLevels (MultiplicityWordSpace (WordMultiplicity ΩA) E F) H)
  (ΩD : E) (hΩD : ‖ΩD‖ = 1)

theorem baseWordInclusion_compression (Y : H →L[ℂ] H)
    (T : WordMultiplicity ΩA 0 →L[ℂ] WordMultiplicity ΩA 0)
    (hY : ∀ v, Y (U.inclusion 0 (hilbertTensorInsert v (emptyEndpoint (F := F) ΩD))) =
      U.inclusion 0 (hilbertTensorInsert (T v) (emptyEndpoint (F := F) ΩD))) :
    (baseWordInclusion ΩA U ΩD hΩD).toContinuousLinearMap.adjoint.comp
      (Y.comp (baseWordInclusion ΩA U ΩD hΩD).toContinuousLinearMap) =
        zeroMultiplicityOperator ΩA T := by
  sorry

end KadisonSimilarity

end

end OAI
end
