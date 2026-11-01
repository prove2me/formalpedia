-- Prove2me | Theorems.Thm_OAI_KadisonSimilarity_TracialCornerGeometry_tracial_word_level_ranges
-- name    : OAI.KadisonSimilarity.TracialCornerGeometry.tracial_word_level_ranges
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-31T09:09:03.162994+00:00
-- url     : https://prove2.me/theorems/968d2272-42c7-4796-90a1-289af1735062
-- title:
--   OAI.KadisonSimilarity.TracialCornerGeometry.tracial_word_level_ranges: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KadisonSimilarity.similarityTheorem`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KadisonSimilarity.TracialCornerGeometry.tracial_word_level_ranges` of [lean/OAI/Analysis/KadisonSimilarity/FreeProduct/TracialFreeCornerEstimate.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/FreeProduct/TracialFreeCornerEstimate.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KadisonSimilarity.TracialCornerGeometry`):
--
--   ```lean
--   theorem tracial_word_level_ranges :
--       (∀ n x, Y (U.inclusion n x) ∈ (U.inclusion n).toLinearMap.range) ∧
--       (∀ n x, Y.adjoint (U.inclusion n x) ∈ (U.inclusion n).toLinearMap.range)
--   ```
--
--   **Definitions.** The statement is written with `OAI.closedSubmoduleInner`, `OAI.closedSubmoduleNormedAddCommGroup`, `OAI.closedSubmoduleNormedSpace`, `OAI.KadisonSimilarity.CompletedTensorWord`, `OAI.KadisonSimilarity.NestedTracialMatrices`, `OAI.KadisonSimilarity.OrthogonalWordLevels`, `OAI.KadisonSimilarity.TensorWord`, `OAI.KadisonSimilarity.TracialCornerGeometry`, `OAI.KadisonSimilarity.centeredSubspace`, `OAI.KadisonSimilarity.hilbertTensorInnerProductSpace`, `OAI.KadisonSimilarity.hilbertTensorNormedAddCommGroup`, `OAI.KadisonSimilarity.tensorWordSpace` and `OAI.KadisonSimilarity.TensorWordSpace` (definitions bundle `OAIQ075A004` of this split); `OAI.KadisonSimilarity.RealTracialSequence` (definitions bundle `OAIQ075A005` of this split); `OAI.KadisonSimilarity.EndpointTensor` (definitions bundle `OAIQ075A009` of this split); `OAI.KadisonSimilarity.MultiplicityWordSpace`, `OAI.KadisonSimilarity.WordMultiplicity`, `OAI.KadisonSimilarity.TracialCornerGeometry.FactorsTraciallyGenerate`, `OAI.KadisonSimilarity.TracialCornerGeometry.baseGeometry`, `OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace` and `OAI.KadisonSimilarity.TracialCornerGeometry.baseVector` (definitions bundle `OAIQ075A016` of this split); `OAI.KadisonSimilarity.TracialCornerGeometry.MatrixConjugationExtensionInput` (definitions bundle `OAIQ075A023` of this split); `OAI.KadisonSimilarity.TracialWordFormula` (definitions bundle `OAIQ075A024` of this split); `OAI.KadisonSimilarity.TracialCornerGeometry.freeCornerMultiplicityInnerFamily`, `OAI.KadisonSimilarity.TracialCornerGeometry.freeCornerMultiplicityNormedFamily` and `OAI.KadisonSimilarity.TracialCornerGeometry.tracialMatrixUnitaryRepresentation` (definitions bundle `OAIQ075A029` of this split).
--
--   **Used by.** The proof of `OAI.KadisonSimilarity.TracialCornerGeometry.free_corner_estimate_of_published_words` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/FreeProduct/TracialFreeCornerEstimate.lean (declaration OAI.KadisonSimilarity.TracialCornerGeometry.tracial_word_level_ranges)

import Mathlib
import Definitions.Def_OAIQ075A029

section

attribute [-instance] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace KadisonSimilarity

universe u v

attribute [local irreducible] TracialCornerGeometry.baseSpace tensorWordSpace

namespace TracialCornerGeometry

variable {P : Type u} {H : Type v} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]
  {I : ℕ → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Nonempty (I j)]
  (M : NestedTracialMatrices (A := I) (G.baseGeometry D).trace (G.baseGeometry D).vector)
  (hgen : G.FactorsTraciallyGenerate A D) (hfaithful : Function.Injective G.vector)
  (hext : ∀ j, G.MatrixConjugationExtensionInput D (M.embedding j) A)
  (S : RealTracialSequence (G.baseGeometry D).trace)
  (hsize : Filter.Tendsto (fun j => (Fintype.card (I j) : ℝ)) Filter.atTop Filter.atTop)

attribute [local instance] OAI.KadisonSimilarity.TracialCornerGeometry.freeCornerMultiplicityNormedFamily
attribute [local instance] OAI.KadisonSimilarity.TracialCornerGeometry.freeCornerMultiplicityInnerFamily
variable (U : OrthogonalWordLevels
    (MultiplicityWordSpace (WordMultiplicity (G.baseVector A 1)) (G.baseSpace D)
      (centeredSubspace (G.baseVector D 1))) H)
  (hword : TracialWordFormula G A D U) (hτ : G.trace 1 = 1)
  (Y : H →L[ℂ] H)
  (hYD : ∀ x : D, Y.comp (G.left (x : P)) = (G.left (x : P)).comp Y)
  (hYU : ∀ j w, Y.comp
    (G.tracialMatrixUnitaryRepresentation A D M hgen hfaithful hext j w : H →L[ℂ] H) =
    (G.tracialMatrixUnitaryRepresentation A D M hgen hfaithful hext j w : H →L[ℂ] H).comp Y)

include S hsize hword hτ hYD hYU in
theorem tracial_word_level_ranges :
    (∀ n x, Y (U.inclusion n x) ∈ (U.inclusion n).toLinearMap.range) ∧
    (∀ n x, Y.adjoint (U.inclusion n x) ∈ (U.inclusion n).toLinearMap.range) := by
  sorry

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end
