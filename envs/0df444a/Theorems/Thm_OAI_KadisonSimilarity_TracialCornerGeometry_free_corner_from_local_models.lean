-- Prove2me | Theorems.Thm_OAI_KadisonSimilarity_TracialCornerGeometry_free_corner_from_local_models
-- name    : OAI.KadisonSimilarity.TracialCornerGeometry.free_corner_from_local_models
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-31T08:57:29.549493+00:00
-- url     : https://prove2.me/theorems/9551c6d2-55ed-46d1-ac11-5676703b481b
-- title:
--   OAI.KadisonSimilarity.TracialCornerGeometry.free_corner_from_local_models: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KadisonSimilarity.similarityTheorem`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KadisonSimilarity.TracialCornerGeometry.free_corner_from_local_models` of [lean/OAI/Analysis/KadisonSimilarity/FreeProduct/TracialFreeCornerTheorem.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/FreeProduct/TracialFreeCornerTheorem.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KadisonSimilarity.TracialCornerGeometry`):
--
--   ```lean
--   theorem free_corner_from_local_models (Y : H →L[ℂ] H)
--       (hYD : ∀ x : D, Y.comp (G.left (x : P)) = (G.left (x : P)).comp Y)
--       (hYU : ∀ j w, Y.comp
--         (G.tracialMatrixUnitaryRepresentation A D M hgen hfaithful hext j w : H →L[ℂ] H) =
--         (G.tracialMatrixUnitaryRepresentation A D M hgen hfaithful hext j w : H →L[ℂ] H).comp Y)
--       {ε : ℝ} (hε : 0 ≤ ε) (hcorner : G.TraceCornerBound D Y t ε) :
--       ‖commutator (G.baseOperator A Y) (G.baseRepresentation A s)‖ ≤
--         6 * Real.pi ^ 2 * (1 + 4 * cyclicConstant) * ε
--   ```
--
--   **Definitions.** The statement is written with `OAI.closedSubmoduleInner`, `OAI.closedSubmoduleNormedAddCommGroup`, `OAI.closedSubmoduleNormedSpace`, `OAI.KadisonSimilarity.CStarCorner`, `OAI.KadisonSimilarity.CompletedTensorWord`, `OAI.KadisonSimilarity.FiniteFactorProjectionComparison`, `OAI.KadisonSimilarity.HaarCornerMoments`, `OAI.KadisonSimilarity.NestedTracialMatrices`, `OAI.KadisonSimilarity.OrthogonalWordLevels`, `OAI.KadisonSimilarity.ScalarFree`, `OAI.KadisonSimilarity.TensorWord`, `OAI.KadisonSimilarity.TracialCornerGeometry`, `OAI.KadisonSimilarity.TracialExpectation`, `OAI.KadisonSimilarity.centeredSubspace`, `OAI.KadisonSimilarity.cstarCornerSubalgebra_closed`, `OAI.KadisonSimilarity.dihedralHalfProjection`, `OAI.KadisonSimilarity.hilbertTensorInnerProductSpace`, `OAI.KadisonSimilarity.hilbertTensorNormedAddCommGroup`, `OAI.KadisonSimilarity.symmetryUnit`, `OAI.KadisonSimilarity.tensorWordSpace`, `OAI.KadisonSimilarity.CStarCorner.instAlgebraComplexSubtypeMemNonUnitalStarSubalgebra`, `OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex`, `OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex`, `OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex`, `OAI.KadisonSimilarity.CStarCorner.instStarOrderedRingSubtypeMemNonUnitalStarSubalgebraComplex`, `OAI.KadisonSimilarity.CStarCorner.normalizedTrace`, `OAI.KadisonSimilarity.CStarCorner.subalgebra`, `OAI.KadisonSimilarity.TensorWordSpace` and `OAI.KadisonSimilarity.TracialCornerGeometry.factorAlgebra` (definitions bundle `OAIQ075A004` of this split); `OAI.KadisonSimilarity.RealTracialSequence`, `OAI.KadisonSimilarity.TracialCommutationInput`, `OAI.KadisonSimilarity.TracialRightSupportInput` and `OAI.KadisonSimilarity.isClosed_comap_subtype` (definitions bundle `OAIQ075A005` of this split); `OAI.KadisonSimilarity.EndpointTensor` (definitions bundle `OAIQ075A009` of this split); `OAI.KadisonSimilarity.DihedralSpectralArcInput` (definitions bundle `OAIQ075A010` of this split); `OAI.KadisonSimilarity.MultiplicityWordSpace`, `OAI.KadisonSimilarity.ReducedWordGenerated`, `OAI.KadisonSimilarity.WordMultiplicity`, `OAI.KadisonSimilarity.CStarCorner.isClosed_subalgebra`, `OAI.KadisonSimilarity.TracialCornerGeometry.FactorsTraciallyGenerate`, `OAI.KadisonSimilarity.TracialCornerGeometry.baseGeometry`, `OAI.KadisonSimilarity.TracialCornerGeometry.baseOperator`, `OAI.KadisonSimilarity.TracialCornerGeometry.baseRepresentation`, `OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace`, `OAI.KadisonSimilarity.TracialCornerGeometry.baseVector` and `OAI.KadisonSimilarity.TracialCornerGeometry.corner` (definitions bundle `OAIQ075A016` of this split); `OAI.KadisonSimilarity.PublishedDerivationInputs` (definitions bundle `OAIQ075A017` of this split); `OAI.KadisonSimilarity.TracialCornerGeometry.MatrixConjugationExtensionInput` (definitions bundle `OAIQ075A023` of this split); `OAI.KadisonSimilarity.RicardXuCompressionInput`, `OAI.KadisonSimilarity.RicardXuCreationInput`, `OAI.KadisonSimilarity.TracialWordFormula` and `OAI.KadisonSimilarity.TracialCornerGeometry.faithfulRightAction` (definitions bundle `OAIQ075A024` of this split); `OAI.KadisonSimilarity.TracialCornerGeometry.TraceCornerBound`, `OAI.KadisonSimilarity.TracialCornerGeometry.assembledMultiplicityInnerFamily` and `OAI.KadisonSimilarity.TracialCornerGeometry.assembledMultiplicityNormedFamily` (definitions bundle `OAIQ075A028` of this split); `OAI.KadisonSimilarity.TracialCornerGeometry.halfCornerGeometry` and `OAI.KadisonSimilarity.TracialCornerGeometry.tracialMatrixUnitaryRepresentation` (definitions bundle `OAIQ075A029` of this split); `OAI.KadisonSimilarity.commutator` and `OAI.KadisonSimilarity.cyclicConstant` (the published bundle `Def_KadisonSimilarity`).
--
--   **Used by.** The proof of `OAI.KadisonSimilarity.TracialCornerGeometry.free_corner_of_published_local_models` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/FreeProduct/TracialFreeCornerTheorem.lean (declaration OAI.KadisonSimilarity.TracialCornerGeometry.free_corner_from_local_models)

import Mathlib
import Definitions.Def_KadisonSimilarity
import Definitions.Def_OAIQ075A028
import Definitions.Def_OAIQ075A029

section

attribute [-instance] _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

attribute [local instance] OAI.KadisonSimilarity.TracialCornerGeometry.assembledMultiplicityNormedFamily
attribute [local instance] OAI.KadisonSimilarity.TracialCornerGeometry.assembledMultiplicityInnerFamily
variable (U : OrthogonalWordLevels
    (MultiplicityWordSpace (WordMultiplicity (G.baseVector A 1)) (G.baseSpace D)
      (centeredSubspace (G.baseVector D 1))) H)
  (hword : TracialWordFormula G A D U) (hτ : G.trace 1 = 1)
  (creation : RicardXuCreationInput G A D) (hf : ScalarFree G.trace D A)
  (hdense : ReducedWordGenerated G A D)
  {q : D} {hq : IsStarProjection q} (z : unitary (CStarCorner q hq))
  {a : ℝ} (ha : 0 < a) (htrace : G.trace (q : P) = (a : ℂ))
  (hhaar : HaarCornerMoments (G.baseGeometry D).trace z a)
  (τ : P → ℝ) (support : TracialRightSupportInput τ (q : P) A)
  (comparison : FiniteFactorProjectionComparison τ)
  (d : D) (s : A) (e : D)
  (hdstar : star d = d) (hdsq : d * d = 1) (hd0 : G.trace (d : P) = 0)
  (hsstar : star s = s) (hssq : s * s = 1) (hs0 : G.trace (s : P) = 0)
  (he : IsStarProjection e) {t : ℝ} (ht : 0 < t) (hte : G.trace (e : P) = (t : ℂ))

variable (hqe : τ (q : P) ≤ τ (e : P))
  {N₀ : ℕ} (hN₀ : 0 < N₀) (frame : Fin N₀ → D)
  (hframe : ∀ i j, star (frame i : P) * (frame j : P) = if i = j then (e : P) else 0)
  (hsum : ∑ i, (frame i : P) * star (frame i : P) = 1)
  (published : PublishedDerivationInputs.{u,v} (CStarCorner (e : P) (show IsStarProjection (e : P) from ⟨congrArg (fun x : D => (x : P)) he.isIdempotentElem.eq, congrArg (fun x : D => (x : P)) he.isSelfAdjoint.star_eq⟩)))
  (commutation : TracialCommutationInput G.left (G.faithfulRightAction hfaithful))
  (C R : StarSubalgebra ℂ P) [IsClosed (C : Set P)]
  (hp : IsStarProjection (dihedralHalfProjection
    (symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq))))
  (hpD : dihedralHalfProjection
    (symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq)) ∈ D)
  (hpC : dihedralHalfProjection
    (symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq)) ∈ C)
  (htp : G.trace (dihedralHalfProjection
    (symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq))) = (1 / 2 : ℂ))

variable (K : StarSubalgebra ℂ (CStarCorner (dihedralHalfProjection (symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq))) hp))
  [IsClosed (K : Set (CStarCorner (dihedralHalfProjection (symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq))) hp))]
  (hK : (factorAlgebra (CStarCorner.subalgebra (dihedralHalfProjection (symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq))) hp D hpD) (CStarCorner.subalgebra (dihedralHalfProjection (symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq))) hp C hpC)).topologicalClosure = K)
  (compression : RicardXuCompressionInput ((G.halfCornerGeometry (symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq)) hp htp).baseGeometry K)
    ((CStarCorner.subalgebra (dihedralHalfProjection (symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq))) hp D hpD).comap K.subtype) ((CStarCorner.subalgebra (dihedralHalfProjection (symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq))) hp C hpC).comap K.subtype))
  (E : TracialExpectation G.trace A) (EC : TracialExpectation G.trace C)
  (hCR : C ≤ R) (hDR : D ≤ R)
  (hdC : (d : P) ∈ C) (hsC : (s : P) ∈ C)
  (hRdense : ∀ x, x ∈ R → G.vector x ∈ (Submodule.span ℂ
    (G.vector '' (StarAlgebra.adjoin ℂ ((D : Set P) ∪ {(s : P)}) : Set P))).topologicalClosure)
  (hpower : ∀ j : ℤ, (↑(((symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq)) * (symmetryUnit (s : P) (congrArg (fun x : A => (x : P)) hssq))) ^ j) : P) ∈ C)
  (hfree : ScalarFree (CStarCorner.normalizedTrace (dihedralHalfProjection (symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq))) hp G.trace) (CStarCorner.subalgebra (dihedralHalfProjection (symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq))) hp D hpD) (CStarCorner.subalgebra (dihedralHalfProjection (symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq))) hp C hpC))
  (hep : (dihedralHalfProjection (symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq))) * (e : P) = (e : P)) (hpe : (e : P) * (dihedralHalfProjection (symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq))) = (e : P))
  (spectral : DihedralSpectralArcInput G.trace C ((symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq)) * (symmetryUnit (s : P) (congrArg (fun x : A => (x : P)) hssq))) (symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq)))

include hgen hext S hsize hword hτ creation hf hdense ha htrace hhaar support comparison
  hdstar hd0 hsstar hs0 ht hte hqe hN₀ hframe hsum published commutation
  hK compression E EC hCR hDR hfaithful hdC hsC hRdense hpower hfree hep hpe spectral in
theorem free_corner_from_local_models (Y : H →L[ℂ] H)
    (hYD : ∀ x : D, Y.comp (G.left (x : P)) = (G.left (x : P)).comp Y)
    (hYU : ∀ j w, Y.comp
      (G.tracialMatrixUnitaryRepresentation A D M hgen hfaithful hext j w : H →L[ℂ] H) =
      (G.tracialMatrixUnitaryRepresentation A D M hgen hfaithful hext j w : H →L[ℂ] H).comp Y)
    {ε : ℝ} (hε : 0 ≤ ε) (hcorner : G.TraceCornerBound D Y t ε) :
    ‖commutator (G.baseOperator A Y) (G.baseRepresentation A s)‖ ≤
      6 * Real.pi ^ 2 * (1 + 4 * cyclicConstant) * ε := by
  sorry

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end
