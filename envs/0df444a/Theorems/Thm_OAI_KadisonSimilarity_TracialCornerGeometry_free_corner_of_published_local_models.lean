-- Prove2me | Theorems.Thm_OAI_KadisonSimilarity_TracialCornerGeometry_free_corner_of_published_local_models
-- name    : OAI.KadisonSimilarity.TracialCornerGeometry.free_corner_of_published_local_models
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-31T09:02:58.674968+00:00
-- url     : https://prove2.me/theorems/4344f9ba-4224-4941-a90b-753a2b154ad0
-- title:
--   OAI.KadisonSimilarity.TracialCornerGeometry.free_corner_of_published_local_models: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KadisonSimilarity.similarityTheorem`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KadisonSimilarity.TracialCornerGeometry.free_corner_of_published_local_models` of [lean/OAI/Analysis/KadisonSimilarity/FreeProduct/TracialFreeCornerModel.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/FreeProduct/TracialFreeCornerModel.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KadisonSimilarity.TracialCornerGeometry`):
--
--   ```lean
--   theorem free_corner_of_published_local_models
--       (hdC : (d : P) ∈ C) (hsC : (s : P) ∈ C)
--       (K : StarSubalgebra ℂ (CStarCorner p (symmetryHalfProjectionProof d hdstar hdsq)))
--       [IsClosed (K : Set (CStarCorner p (symmetryHalfProjectionProof d hdstar hdsq)))]
--       (hK : (factorAlgebra
--         (CStarCorner.subalgebra p (symmetryHalfProjectionProof d hdstar hdsq) D
--           (symmetryHalfProjection_mem D d hdsq d.property))
--         (CStarCorner.subalgebra p (symmetryHalfProjectionProof d hdstar hdsq) C
--           (symmetryHalfProjection_mem C d hdsq hdC))).topologicalClosure = K)
--       (compression : RicardXuCompressionInput
--         ((G.halfCornerGeometry dU (symmetryHalfProjectionProof d hdstar hdsq)
--           (trace_dihedralHalfProjection G.trace hτ dU hd0)).baseGeometry K)
--         ((CStarCorner.subalgebra p (symmetryHalfProjectionProof d hdstar hdsq) D
--           (symmetryHalfProjection_mem D d hdsq d.property)).comap K.subtype)
--         ((CStarCorner.subalgebra p (symmetryHalfProjectionProof d hdstar hdsq) C
--           (symmetryHalfProjection_mem C d hdsq hdC)).comap K.subtype))
--       (E : TracialExpectation G.trace A) (EC : TracialExpectation G.trace C)
--       (hCR : C ≤ R) (hDR : D ≤ R)
--       (hRdense : ∀ x, x ∈ R → G.vector x ∈ (Submodule.span ℂ
--         (G.vector '' (StarAlgebra.adjoin ℂ ((D : Set P) ∪ {(s : P)}) : Set P))).topologicalClosure)
--       (hCdense : ∀ x, x ∈ C → G.vector x ∈ (Submodule.span ℂ
--         (G.vector '' (StarAlgebra.adjoin ℂ ({(d : P), (s : P)} : Set P) : Set P))).topologicalClosure)
--       (hep : p * (e : P) = (e : P)) (hpe : (e : P) * p = (e : P))
--       (spectral : DihedralSpectralArcInput G.trace C (dU * sU) dU)
--       (T : H →L[ℂ] H)
--       (hTD : ∀ x : D, T.comp (G.left (x : P)) = (G.left (x : P)).comp T)
--       {ε : ℝ} (hε : 0 ≤ ε) (hcorner : G.TraceCornerBound D T t ε) :
--       ‖G.baseOperator A (commutator T (G.left (s : P)))‖ ≤
--         6 * Real.pi ^ 2 * (1 + 4 * cyclicConstant) * ε
--   ```
--
--   **Definitions.** The statement is written with `OAI.closedSubmoduleInner`, `OAI.closedSubmoduleNormedAddCommGroup`, `OAI.closedSubmoduleNormedSpace`, `OAI.KadisonSimilarity.CStarCorner`, `OAI.KadisonSimilarity.FiniteFactorProjectionComparison`, `OAI.KadisonSimilarity.HaarCornerMoments`, `OAI.KadisonSimilarity.NestedTracialMatrices`, `OAI.KadisonSimilarity.ScalarFree`, `OAI.KadisonSimilarity.TracialCornerGeometry`, `OAI.KadisonSimilarity.TracialExpectation`, `OAI.KadisonSimilarity.cstarCornerSubalgebra_closed`, `OAI.KadisonSimilarity.dihedralHalfProjection`, `OAI.KadisonSimilarity.symmetryUnit`, `OAI.KadisonSimilarity.CStarCorner.instAlgebraComplexSubtypeMemNonUnitalStarSubalgebra`, `OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex`, `OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex`, `OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex`, `OAI.KadisonSimilarity.CStarCorner.instStarOrderedRingSubtypeMemNonUnitalStarSubalgebraComplex`, `OAI.KadisonSimilarity.CStarCorner.subalgebra` and `OAI.KadisonSimilarity.TracialCornerGeometry.factorAlgebra` (definitions bundle `OAIQ075A004` of this split); `OAI.KadisonSimilarity.RealTracialSequence`, `OAI.KadisonSimilarity.TracialCommutationInput`, `OAI.KadisonSimilarity.TracialRightSupportInput` and `OAI.KadisonSimilarity.isClosed_comap_subtype` (definitions bundle `OAIQ075A005` of this split); `OAI.KadisonSimilarity.DihedralSpectralArcInput` (definitions bundle `OAIQ075A010` of this split); `OAI.KadisonSimilarity.trace_dihedralHalfProjection` (definitions bundle `OAIQ075A011` of this split); `OAI.KadisonSimilarity.CStarCorner.isClosed_subalgebra`, `OAI.KadisonSimilarity.TracialCornerGeometry.FactorsTraciallyGenerate`, `OAI.KadisonSimilarity.TracialCornerGeometry.baseGeometry`, `OAI.KadisonSimilarity.TracialCornerGeometry.baseOperator`, `OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace` and `OAI.KadisonSimilarity.TracialCornerGeometry.corner` (definitions bundle `OAIQ075A016` of this split); `OAI.KadisonSimilarity.PublishedDerivationInputs` (definitions bundle `OAIQ075A017` of this split); `OAI.KadisonSimilarity.TracialCornerGeometry.MatrixConjugationExtensionInput` (definitions bundle `OAIQ075A023` of this split); `OAI.KadisonSimilarity.RicardXuCompressionInput`, `OAI.KadisonSimilarity.RicardXuCreationInput`, `OAI.KadisonSimilarity.RicardXuWordDecompositionInput`, `OAI.KadisonSimilarity.symmetryHalfProjectionProof`, `OAI.KadisonSimilarity.symmetryHalfProjection_mem` and `OAI.KadisonSimilarity.TracialCornerGeometry.faithfulRightAction` (definitions bundle `OAIQ075A024` of this split); `OAI.KadisonSimilarity.TracialCornerGeometry.TraceCornerBound` (definitions bundle `OAIQ075A028` of this split); `OAI.KadisonSimilarity.TracialCornerGeometry.halfCornerGeometry` (definitions bundle `OAIQ075A029` of this split); `OAI.KadisonSimilarity.commutator` and `OAI.KadisonSimilarity.cyclicConstant` (the published bundle `Def_KadisonSimilarity`).
--
--   **Used by.** The proof of `OAI.KadisonSimilarity.TracialCornerGeometry.free_corner_from_local_published_inputs` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/FreeProduct/TracialFreeCornerModel.lean (declaration OAI.KadisonSimilarity.TracialCornerGeometry.free_corner_of_published_local_models)

import Mathlib
import Definitions.Def_KadisonSimilarity
import Definitions.Def_OAIQ075A028
import Definitions.Def_OAIQ075A029

section

attribute [-instance] _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.canonicalGeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.jointCStarSource_isClosed _root_.OAI.KadisonSimilarity.sequenceGeneratedCStarAlgebra_isClosed _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace KadisonSimilarity

universe u v

variable {P : Type u} [CStarAlgebra P]

attribute [local irreducible] TracialCornerGeometry.baseSpace tensorWordSpace

namespace TracialCornerGeometry

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]
  {I : ℕ → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Nonempty (I j)]
  (M : NestedTracialMatrices (A := I) (G.baseGeometry D).trace (G.baseGeometry D).vector)
  (hgen : G.FactorsTraciallyGenerate A D) (hfaithful : Function.Injective G.vector)
  (hext : ∀ j, G.MatrixConjugationExtensionInput D (M.embedding j) A)
  (S : RealTracialSequence (G.baseGeometry D).trace)
  (hsize : Filter.Tendsto (fun j => (Fintype.card (I j) : ℝ)) Filter.atTop Filter.atTop)
  (hτ : G.trace 1 = 1) (hf : ScalarFree G.trace D A)
  (words : RicardXuWordDecompositionInput G A D)
  (creation : RicardXuCreationInput G A D)
  {q : D} {hq : IsStarProjection q} (z : unitary (CStarCorner q hq))
  {a : ℝ} (ha : 0 < a) (htrace : G.trace (q : P) = (a : ℂ))
  (hhaar : HaarCornerMoments (G.baseGeometry D).trace z a)
  (τ : P → ℝ) (support : TracialRightSupportInput τ (q : P) A)
  (comparison : FiniteFactorProjectionComparison τ)
  (d : D) (s : A) (e : D)
  (hdstar : star d = d) (hdsq : d * d = 1) (hd0 : G.trace (d : P) = 0)
  (hsstar : star s = s) (hssq : s * s = 1) (hs0 : G.trace (s : P) = 0)
  (he : IsStarProjection e) {t : ℝ} (ht : 0 < t) (hte : G.trace (e : P) = (t : ℂ))
  (hqe : τ (q : P) ≤ τ (e : P))
  {N₀ : ℕ} (hN₀ : 0 < N₀) (frame : Fin N₀ → D)
  (hframe : ∀ i j, star (frame i : P) * (frame j : P) = if i = j then (e : P) else 0)
  (hsum : ∑ i, (frame i : P) * star (frame i : P) = 1)
  (published : PublishedDerivationInputs.{u,v} (CStarCorner (e : P)
    ⟨congrArg (fun x : D => (x : P)) he.isIdempotentElem.eq,
      congrArg (fun x : D => (x : P)) he.isSelfAdjoint.star_eq⟩))
  (commutation : TracialCommutationInput G.left (G.faithfulRightAction hfaithful))
  (C R : StarSubalgebra ℂ P) [IsClosed (C : Set P)]

local notation "dU" => symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq)
local notation "sU" => symmetryUnit (s : P) (congrArg (fun x : A => (x : P)) hssq)
local notation "p" => dihedralHalfProjection
  (symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq))

include hgen hfaithful hext S hsize hτ hf words creation ha htrace hhaar support
  comparison hdstar hd0 hsstar hs0 ht hte hqe hN₀ hframe hsum published commutation in
theorem free_corner_of_published_local_models
    (hdC : (d : P) ∈ C) (hsC : (s : P) ∈ C)
    (K : StarSubalgebra ℂ (CStarCorner p (symmetryHalfProjectionProof d hdstar hdsq)))
    [IsClosed (K : Set (CStarCorner p (symmetryHalfProjectionProof d hdstar hdsq)))]
    (hK : (factorAlgebra
      (CStarCorner.subalgebra p (symmetryHalfProjectionProof d hdstar hdsq) D
        (symmetryHalfProjection_mem D d hdsq d.property))
      (CStarCorner.subalgebra p (symmetryHalfProjectionProof d hdstar hdsq) C
        (symmetryHalfProjection_mem C d hdsq hdC))).topologicalClosure = K)
    (compression : RicardXuCompressionInput
      ((G.halfCornerGeometry dU (symmetryHalfProjectionProof d hdstar hdsq)
        (trace_dihedralHalfProjection G.trace hτ dU hd0)).baseGeometry K)
      ((CStarCorner.subalgebra p (symmetryHalfProjectionProof d hdstar hdsq) D
        (symmetryHalfProjection_mem D d hdsq d.property)).comap K.subtype)
      ((CStarCorner.subalgebra p (symmetryHalfProjectionProof d hdstar hdsq) C
        (symmetryHalfProjection_mem C d hdsq hdC)).comap K.subtype))
    (E : TracialExpectation G.trace A) (EC : TracialExpectation G.trace C)
    (hCR : C ≤ R) (hDR : D ≤ R)
    (hRdense : ∀ x, x ∈ R → G.vector x ∈ (Submodule.span ℂ
      (G.vector '' (StarAlgebra.adjoin ℂ ((D : Set P) ∪ {(s : P)}) : Set P))).topologicalClosure)
    (hCdense : ∀ x, x ∈ C → G.vector x ∈ (Submodule.span ℂ
      (G.vector '' (StarAlgebra.adjoin ℂ ({(d : P), (s : P)} : Set P) : Set P))).topologicalClosure)
    (hep : p * (e : P) = (e : P)) (hpe : (e : P) * p = (e : P))
    (spectral : DihedralSpectralArcInput G.trace C (dU * sU) dU)
    (T : H →L[ℂ] H)
    (hTD : ∀ x : D, T.comp (G.left (x : P)) = (G.left (x : P)).comp T)
    {ε : ℝ} (hε : 0 ≤ ε) (hcorner : G.TraceCornerBound D T t ε) :
    ‖G.baseOperator A (commutator T (G.left (s : P)))‖ ≤
      6 * Real.pi ^ 2 * (1 + 4 * cyclicConstant) * ε := by
  sorry

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end
