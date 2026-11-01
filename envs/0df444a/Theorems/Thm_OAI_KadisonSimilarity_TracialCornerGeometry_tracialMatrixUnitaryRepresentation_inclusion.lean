-- Prove2me | Theorems.Thm_OAI_KadisonSimilarity_TracialCornerGeometry_tracialMatrixUnitaryRepresentation_inclusion
-- name    : OAI.KadisonSimilarity.TracialCornerGeometry.tracialMatrixUnitaryRepresentation_inclusion
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-31T09:08:09.686788+00:00
-- url     : https://prove2.me/theorems/fd127b3a-2834-4992-aa7e-3d0be3a9ea74
-- title:
--   OAI.KadisonSimilarity.TracialCornerGeometry.tracialMatrixUnitaryRepresentation_inclusion (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KadisonSimilarity.similarityTheorem`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KadisonSimilarity.TracialCornerGeometry.tracialMatrixUnitaryRepresentation_inclusion` of [lean/OAI/Analysis/KadisonSimilarity/FreeProduct/TracialEmbeddedWordStructure.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/FreeProduct/TracialEmbeddedWordStructure.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KadisonSimilarity.TracialCornerGeometry`):
--
--   ```lean
--   theorem tracialMatrixUnitaryRepresentation_inclusion (s : ℕ)
--       (u : Matrix.unitaryGroup (I s) ℂ) (n : ℕ) :
--       (G.tracialMatrixUnitaryRepresentation A D M hgen hfaithful hext s u : H →L[ℂ] H).comp
--           (U.inclusion n).toContinuousLinearMap =
--         (U.inclusion n).toContinuousLinearMap.comp
--           (hilbertTensorLift (tracialMatrixWordAction (G.baseGeometry D).trace
--             (G.baseGeometry D).vector (G.baseGeometry D).left (M.embedding s)
--             (G.baseGeometry D).inner_vector (G.baseGeometry D).left_vector
--             (G.baseGeometry D).tracial
--             (NestedTracialMatrices.denseRange_vector (G.baseGeometry D).trace
--               (G.baseGeometry D).vector M) u n).toContinuousLinearMap)
--   ```
--
--   **Definitions.** The statement is written with `OAI.closedSubmoduleInner`, `OAI.closedSubmoduleNormedAddCommGroup`, `OAI.closedSubmoduleNormedSpace`, `OAI.KadisonSimilarity.CompletedTensorWord`, `OAI.KadisonSimilarity.HilbertTensor`, `OAI.KadisonSimilarity.NestedTracialMatrices`, `OAI.KadisonSimilarity.OrthogonalWordLevels`, `OAI.KadisonSimilarity.TensorWord`, `OAI.KadisonSimilarity.TracialCornerGeometry`, `OAI.KadisonSimilarity.centeredSubspace`, `OAI.KadisonSimilarity.hilbertTensorInnerProductSpace`, `OAI.KadisonSimilarity.hilbertTensorNormedAddCommGroup`, `OAI.KadisonSimilarity.tensorWordSpace` and `OAI.KadisonSimilarity.TensorWordSpace` (definitions bundle `OAIQ075A004` of this split); `OAI.KadisonSimilarity.EndpointTensor` (definitions bundle `OAIQ075A009` of this split); `OAI.KadisonSimilarity.NestedTracialMatrices.denseRange_vector` (definitions bundle `OAIQ075A011` of this split); `OAI.KadisonSimilarity.MultiplicityWordSpace`, `OAI.KadisonSimilarity.WordMultiplicity`, `OAI.KadisonSimilarity.hilbertTensorLift`, `OAI.KadisonSimilarity.TracialCornerGeometry.FactorsTraciallyGenerate`, `OAI.KadisonSimilarity.TracialCornerGeometry.baseGeometry`, `OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace` and `OAI.KadisonSimilarity.TracialCornerGeometry.baseVector` (definitions bundle `OAIQ075A016` of this split); `OAI.KadisonSimilarity.TracialCornerGeometry.MatrixConjugationExtensionInput` (definitions bundle `OAIQ075A023` of this split); `OAI.KadisonSimilarity.TracialWordFormula` and `OAI.KadisonSimilarity.tracialMatrixWordAction` (definitions bundle `OAIQ075A024` of this split); `OAI.KadisonSimilarity.TracialCornerGeometry.tracialEmbeddedMultiplicityInnerFamily`, `OAI.KadisonSimilarity.TracialCornerGeometry.tracialEmbeddedMultiplicityNormedFamily` and `OAI.KadisonSimilarity.TracialCornerGeometry.tracialMatrixUnitaryRepresentation` (definitions bundle `OAIQ075A029` of this split).
--
--   **Used by.** The proofs of `OAI.KadisonSimilarity.TracialCornerGeometry.tracial_adjoint_repeated_word`, `OAI.KadisonSimilarity.TracialCornerGeometry.tracial_repeated_word` and `OAI.KadisonSimilarity.TracialCornerGeometry.tracial_word_level_ranges` of this split import it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/FreeProduct/TracialEmbeddedWordStructure.lean (declaration OAI.KadisonSimilarity.TracialCornerGeometry.tracialMatrixUnitaryRepresentation_inclusion)

import Mathlib
import Definitions.Def_OAIQ075A029

section

attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace KadisonSimilarity
namespace TracialCornerGeometry

attribute [local irreducible] TracialCornerGeometry.baseSpace tensorWordSpace

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]
  {I : ℕ → Type*} [∀ s, Fintype (I s)] [∀ s, DecidableEq (I s)]
  [∀ s, Nonempty (I s)]
  (M : NestedTracialMatrices (A := I) (G.baseGeometry D).trace (G.baseGeometry D).vector)

variable (hgen : G.FactorsTraciallyGenerate A D) (hfaithful : Function.Injective G.vector)
  (hext : ∀ s, G.MatrixConjugationExtensionInput D (M.embedding s) A)

variable (S : RealTracialSequence (G.baseGeometry D).trace)
  (hsize : Filter.Tendsto (fun s => (Fintype.card (I s) : ℝ)) Filter.atTop Filter.atTop)

attribute [local instance] OAI.KadisonSimilarity.TracialCornerGeometry.tracialEmbeddedMultiplicityNormedFamily
attribute [local instance] OAI.KadisonSimilarity.TracialCornerGeometry.tracialEmbeddedMultiplicityInnerFamily
variable (U : OrthogonalWordLevels
    (MultiplicityWordSpace (WordMultiplicity (G.baseVector A 1)) (G.baseSpace D)
      (centeredSubspace (G.baseVector D 1))) H)
  (hword : TracialWordFormula G A D U) (hτ : G.trace 1 = 1)

include hword hτ in
omit [∀ s, Nonempty (I s)] in
theorem tracialMatrixUnitaryRepresentation_inclusion (s : ℕ)
    (u : Matrix.unitaryGroup (I s) ℂ) (n : ℕ) :
    (G.tracialMatrixUnitaryRepresentation A D M hgen hfaithful hext s u : H →L[ℂ] H).comp
        (U.inclusion n).toContinuousLinearMap =
      (U.inclusion n).toContinuousLinearMap.comp
        (hilbertTensorLift (tracialMatrixWordAction (G.baseGeometry D).trace
          (G.baseGeometry D).vector (G.baseGeometry D).left (M.embedding s)
          (G.baseGeometry D).inner_vector (G.baseGeometry D).left_vector
          (G.baseGeometry D).tracial
          (NestedTracialMatrices.denseRange_vector (G.baseGeometry D).trace
            (G.baseGeometry D).vector M) u n).toContinuousLinearMap) := by
  sorry

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end
