-- Prove2me | Theorems.Thm_OAI_KadisonSimilarity_embedded_actions_word_levels_preserved
-- name    : OAI.KadisonSimilarity.embedded_actions_word_levels_preserved
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-03T16:43:48.217048+00:00
-- url     : https://prove2.me/theorems/3b20d5af-fead-4736-934a-1c64a297408c
-- title:
--   OAI.KadisonSimilarity.embedded_actions_word_levels_preserved: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KadisonSimilarity.similarityTheorem`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KadisonSimilarity.embedded_actions_word_levels_preserved` of [lean/OAI/Analysis/KadisonSimilarity/FreeProduct/EmbeddedWordStructure.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/FreeProduct/EmbeddedWordStructure.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KadisonSimilarity`):
--
--   ```lean
--   theorem embedded_actions_word_levels_preserved (n : ℕ) :
--       Y.comp (U.inclusion n).toContinuousLinearMap =
--         (U.inclusion n).toContinuousLinearMap.comp (U.block Y n n)
--   ```
--
--   **Definitions.** The statement is written with `OAI.KadisonSimilarity.CompletedTensorWord`, `OAI.KadisonSimilarity.HilbertTensor`, `OAI.KadisonSimilarity.NestedTracialMatrices`, `OAI.KadisonSimilarity.OrthogonalWordLevels`, `OAI.KadisonSimilarity.TensorWord`, `OAI.KadisonSimilarity.centeredSubspace`, `OAI.KadisonSimilarity.hilbertTensorCompleteSpace`, `OAI.KadisonSimilarity.hilbertTensorInnerProductSpace`, `OAI.KadisonSimilarity.hilbertTensorNormedAddCommGroup`, `OAI.KadisonSimilarity.tensorWordSpace`, `OAI.KadisonSimilarity.MatrixHilbertStage` and `OAI.KadisonSimilarity.TensorWordSpace` (definitions bundle `OAIQ075A004` of this split); `OAI.KadisonSimilarity.RealTracialSequence` (definitions bundle `OAIQ075A005` of this split); `OAI.KadisonSimilarity.EndpointTensor` and `OAI.KadisonSimilarity.endpointHeadAction` (definitions bundle `OAIQ075A009` of this split); `OAI.KadisonSimilarity.NestedTracialMatrices.denseRange_vector` and `OAI.KadisonSimilarity.OrthogonalWordLevels.block` (definitions bundle `OAIQ075A011` of this split); `OAI.KadisonSimilarity.MultiplicityWordSpace` and `OAI.KadisonSimilarity.hilbertTensorLift` (definitions bundle `OAIQ075A016` of this split); `OAI.KadisonSimilarity.tracialMatrixWordAction` (definitions bundle `OAIQ075A024` of this split); `OAI.KadisonSimilarity.TracialMatrixTower` (definitions bundle `OAIQ075A028` of this split); `OAI.KadisonSimilarity.tracialMatrixTowerOfEmbeddings` (definitions bundle `OAIQ075A033` of this split).
--
--   **Used by.** The proof of `OAI.KadisonSimilarity.TracialCornerGeometry.tracial_word_levels_preserved` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/FreeProduct/EmbeddedWordStructure.lean (declaration OAI.KadisonSimilarity.embedded_actions_word_levels_preserved)

import Mathlib
import Definitions.Def_OAIQ075A033

section

attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace KadisonSimilarity

universe u v
variable {R : Type v} {E : Type u}
  [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {A : ℕ → Type*} [∀ s, Fintype (A s)] [∀ s, DecidableEq (A s)]
  [∀ s, Nonempty (A s)]
  (τ : R →ₗ[ℂ] ℂ) (V : R →ₗ[ℂ] E) (L : R →⋆ₐ[ℂ] (E →L[ℂ] E))
  (hinner : ∀ a b, inner ℂ (V a) (V b) = τ (star a * b))
  (hleft : ∀ a b, L a (V b) = V (a * b))
  (M : NestedTracialMatrices (A := A) τ V)
  (htrace : ∀ a b, τ (a * b) = τ (b * a)) (S : RealTracialSequence τ)
  (hsize : Filter.Tendsto (fun s => (Fintype.card (A s) : ℝ)) Filter.atTop Filter.atTop)
  {J : ℕ → Type*} [∀ n, NormedAddCommGroup (J n)] [∀ n, InnerProductSpace ℂ (J n)]
  [∀ n, CompleteSpace (J n)]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : OrthogonalWordLevels (MultiplicityWordSpace J E (centeredSubspace (V 1))) H)
  (leftRep : ∀ s, Matrix (A s) (A s) ℂ →⋆ₐ[ℂ] (H →L[ℂ] H))
  (unitaryRep : ∀ s, Matrix.unitaryGroup (A s) ℂ →* unitary (H →L[ℂ] H))
  (hL : ∀ s a n, (leftRep s a).comp (U.inclusion n).toContinuousLinearMap =
    (U.inclusion n).toContinuousLinearMap.comp
      (hilbertTensorLift (endpointHeadAction (n := n)
        (((tracialMatrixTowerOfEmbeddings τ V L hinner hleft M htrace S hsize).stage s).left a))))
  (hU : ∀ s u n, (unitaryRep s u : H →L[ℂ] H).comp (U.inclusion n).toContinuousLinearMap =
    (U.inclusion n).toContinuousLinearMap.comp
      (hilbertTensorLift (tracialMatrixWordAction τ V L (M.embedding s) hinner hleft htrace
        (NestedTracialMatrices.denseRange_vector τ V M) u n).toContinuousLinearMap))
  (Y : H →L[ℂ] H)
  (hYL : ∀ s a, Y.comp (leftRep s a) = (leftRep s a).comp Y)
  (hYU : ∀ s u, Y.comp (unitaryRep s u : H →L[ℂ] H) =
    (unitaryRep s u : H →L[ℂ] H).comp Y)

include hL hU hYL hYU in
omit [∀ n, CompleteSpace (J n)] in
theorem embedded_actions_word_levels_preserved (n : ℕ) :
    Y.comp (U.inclusion n).toContinuousLinearMap =
      (U.inclusion n).toContinuousLinearMap.comp (U.block Y n n) := by
  sorry

end KadisonSimilarity

end

end OAI
end
