-- Prove2me | Theorems.Thm_OAI_KadisonSimilarity_TracialCornerGeometry_free_corner_estimate_of_published_words
-- name    : OAI.KadisonSimilarity.TracialCornerGeometry.free_corner_estimate_of_published_words
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-31T08:58:20.467814+00:00
-- url     : https://prove2.me/theorems/89da6847-9783-40de-8d8f-98a66ddd3bf8
-- title:
--   OAI.KadisonSimilarity.TracialCornerGeometry.free_corner_estimate_of_published_words (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KadisonSimilarity.similarityTheorem`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KadisonSimilarity.TracialCornerGeometry.free_corner_estimate_of_published_words` of [lean/OAI/Analysis/KadisonSimilarity/FreeProduct/TracialFreeCornerEstimate.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/FreeProduct/TracialFreeCornerEstimate.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KadisonSimilarity.TracialCornerGeometry`):
--
--   ```lean
--   theorem free_corner_estimate_of_published_words
--       (creation : RicardXuCreationInput G A D) (hf : ScalarFree G.trace D A)
--       (hdense : ReducedWordGenerated G A D)
--       {q : D} {hq : IsStarProjection q} (z : unitary (CStarCorner q hq))
--       {a : ℝ} (ha : 0 < a) (htrace : G.trace (q : P) = (a : ℂ))
--       (hhaar : HaarCornerMoments (G.baseGeometry D).trace z a)
--       (τ : P → ℝ) (support : TracialRightSupportInput τ (q : P) A)
--       (e₀ : P) (he₀ : IsStarProjection e₀) (he₀D : e₀ ∈ D)
--       (hqe : τ (q : P) ≤ τ e₀) (comparison : FiniteFactorProjectionComparison τ)
--       {N₀ : ℕ} (hN₀ : 0 < N₀) (frame : Fin N₀ → D)
--       (hframe : ∀ i j, star (frame i : P) * (frame j : P) = if i = j then e₀ else 0)
--       (hsum : ∑ i, (frame i : P) * star (frame i : P) = 1)
--       {ε : ℝ} (hε : 0 ≤ ε)
--       (hcorner : ∀ x : CStarCorner e₀ he₀,
--         ‖commutator Y (G.left (x : P))‖ ≤ ε * ‖x‖)
--       (published : PublishedDerivationInputs.{u,v} (CStarCorner e₀ he₀))
--       (commutation : TracialCommutationInput G.left (G.faithfulRightAction hfaithful))
--       (d : D) (s : A) (e : D)
--       (hdstar : star d = d) (hdsq : d * d = 1) (hd0 : G.trace (d : P) = 0)
--       (hsstar : star s = s) (hssq : s * s = 1) (hs0 : G.trace (s : P) = 0)
--       (he : IsStarProjection e) {t : ℝ} (ht : 0 < t) (hte : G.trace (e : P) = (t : ℂ))
--       (T : H →L[ℂ] H) {N : ℕ} (hN : 0 < N) (toeplitz : Matrix (Fin N) (Fin N) ℝ)
--       {b : ℝ} (hb : 0 < b) (hT : ‖T‖ ≤ 3 * b)
--       (hcomm : ‖commutator Y T‖ ≤ ε * ‖T‖)
--       (hfourier :
--         let V := G.tracialDihedralColumns D A hf hτ d s e hdstar hdsq hd0 hsstar hssq hs0
--           he ht hte N
--         (sumColumns V).adjoint.comp (T.comp (sumColumns V)) =
--           (b : ℂ) • matrixOperator (fun i j =>
--             (toeplitz i j : ℂ) • ContinuousLinearMap.id ℂ (G.baseSpace A) +
--               (arcHankelMatrix N i j : ℂ) • G.baseRepresentation A s)) :
--       ‖commutator (G.baseOperator A Y) (G.baseRepresentation A s)‖ ≤
--         6 * Real.pi ^ 2 * (1 + 4 * cyclicConstant) * ε
--   ```
--
--   **Definitions.** The statement is written with `OAI.closedSubmoduleInner`, `OAI.closedSubmoduleNormedAddCommGroup`, `OAI.closedSubmoduleNormedSpace`, `OAI.KadisonSimilarity.CStarCorner`, `OAI.KadisonSimilarity.CompletedTensorWord`, `OAI.KadisonSimilarity.FiniteFactorProjectionComparison`, `OAI.KadisonSimilarity.HaarCornerMoments`, `OAI.KadisonSimilarity.NestedTracialMatrices`, `OAI.KadisonSimilarity.OrthogonalWordLevels`, `OAI.KadisonSimilarity.ScalarFree`, `OAI.KadisonSimilarity.TensorWord`, `OAI.KadisonSimilarity.TracialCornerGeometry`, `OAI.KadisonSimilarity.centeredSubspace`, `OAI.KadisonSimilarity.hilbertTensorInnerProductSpace`, `OAI.KadisonSimilarity.hilbertTensorNormedAddCommGroup`, `OAI.KadisonSimilarity.sumColumns`, `OAI.KadisonSimilarity.tensorWordSpace`, `OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex`, `OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex`, `OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex`, `OAI.KadisonSimilarity.CStarCorner.instStarOrderedRingSubtypeMemNonUnitalStarSubalgebraComplex` and `OAI.KadisonSimilarity.TensorWordSpace` (definitions bundle `OAIQ075A004` of this split); `OAI.KadisonSimilarity.RealTracialSequence`, `OAI.KadisonSimilarity.TracialCommutationInput` and `OAI.KadisonSimilarity.TracialRightSupportInput` (definitions bundle `OAIQ075A005` of this split); `OAI.KadisonSimilarity.arcHankelMatrix` (definitions bundle `OAIQ075A006` of this split); `OAI.KadisonSimilarity.EndpointTensor` (definitions bundle `OAIQ075A009` of this split); `OAI.KadisonSimilarity.MultiplicityWordSpace`, `OAI.KadisonSimilarity.ReducedWordGenerated`, `OAI.KadisonSimilarity.WordMultiplicity`, `OAI.KadisonSimilarity.TracialCornerGeometry.FactorsTraciallyGenerate`, `OAI.KadisonSimilarity.TracialCornerGeometry.baseGeometry`, `OAI.KadisonSimilarity.TracialCornerGeometry.baseOperator`, `OAI.KadisonSimilarity.TracialCornerGeometry.baseRepresentation`, `OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace` and `OAI.KadisonSimilarity.TracialCornerGeometry.baseVector` (definitions bundle `OAIQ075A016` of this split); `OAI.KadisonSimilarity.PublishedDerivationInputs` (definitions bundle `OAIQ075A017` of this split); `OAI.KadisonSimilarity.TracialCornerGeometry.MatrixConjugationExtensionInput` (definitions bundle `OAIQ075A023` of this split); `OAI.KadisonSimilarity.RicardXuCreationInput`, `OAI.KadisonSimilarity.TracialWordFormula`, `OAI.KadisonSimilarity.TracialCornerGeometry.faithfulRightAction` and `OAI.KadisonSimilarity.TracialCornerGeometry.tracialDihedralColumns` (definitions bundle `OAIQ075A024` of this split); `OAI.KadisonSimilarity.TracialCornerGeometry.freeCornerMultiplicityInnerFamily`, `OAI.KadisonSimilarity.TracialCornerGeometry.freeCornerMultiplicityNormedFamily` and `OAI.KadisonSimilarity.TracialCornerGeometry.tracialMatrixUnitaryRepresentation` (definitions bundle `OAIQ075A029` of this split); `OAI.KadisonSimilarity.HilbertCopies`, `OAI.KadisonSimilarity.commutator`, `OAI.KadisonSimilarity.cyclicConstant` and `OAI.KadisonSimilarity.matrixOperator` (the published bundle `Def_KadisonSimilarity`).
--
--   **Used by.** The proofs of `OAI_KadisonSimilarity_TracialCornerGeometry_free_corner_from_local_models` and `OAI.KadisonSimilarity.TracialCornerGeometry.free_corner_of_published_local_models` of this split import it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/FreeProduct/TracialFreeCornerEstimate.lean (declaration OAI.KadisonSimilarity.TracialCornerGeometry.free_corner_estimate_of_published_words)

import Mathlib
import Definitions.Def_KadisonSimilarity
import Definitions.Def_OAIQ075A029

section

attribute [-instance] _root_.OAI.KadisonSimilarity.CStarCorner.isClosed_subalgebra _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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
theorem free_corner_estimate_of_published_words
    (creation : RicardXuCreationInput G A D) (hf : ScalarFree G.trace D A)
    (hdense : ReducedWordGenerated G A D)
    {q : D} {hq : IsStarProjection q} (z : unitary (CStarCorner q hq))
    {a : ℝ} (ha : 0 < a) (htrace : G.trace (q : P) = (a : ℂ))
    (hhaar : HaarCornerMoments (G.baseGeometry D).trace z a)
    (τ : P → ℝ) (support : TracialRightSupportInput τ (q : P) A)
    (e₀ : P) (he₀ : IsStarProjection e₀) (he₀D : e₀ ∈ D)
    (hqe : τ (q : P) ≤ τ e₀) (comparison : FiniteFactorProjectionComparison τ)
    {N₀ : ℕ} (hN₀ : 0 < N₀) (frame : Fin N₀ → D)
    (hframe : ∀ i j, star (frame i : P) * (frame j : P) = if i = j then e₀ else 0)
    (hsum : ∑ i, (frame i : P) * star (frame i : P) = 1)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hcorner : ∀ x : CStarCorner e₀ he₀,
      ‖commutator Y (G.left (x : P))‖ ≤ ε * ‖x‖)
    (published : PublishedDerivationInputs.{u,v} (CStarCorner e₀ he₀))
    (commutation : TracialCommutationInput G.left (G.faithfulRightAction hfaithful))
    (d : D) (s : A) (e : D)
    (hdstar : star d = d) (hdsq : d * d = 1) (hd0 : G.trace (d : P) = 0)
    (hsstar : star s = s) (hssq : s * s = 1) (hs0 : G.trace (s : P) = 0)
    (he : IsStarProjection e) {t : ℝ} (ht : 0 < t) (hte : G.trace (e : P) = (t : ℂ))
    (T : H →L[ℂ] H) {N : ℕ} (hN : 0 < N) (toeplitz : Matrix (Fin N) (Fin N) ℝ)
    {b : ℝ} (hb : 0 < b) (hT : ‖T‖ ≤ 3 * b)
    (hcomm : ‖commutator Y T‖ ≤ ε * ‖T‖)
    (hfourier :
      let V := G.tracialDihedralColumns D A hf hτ d s e hdstar hdsq hd0 hsstar hssq hs0
        he ht hte N
      (sumColumns V).adjoint.comp (T.comp (sumColumns V)) =
        (b : ℂ) • matrixOperator (fun i j =>
          (toeplitz i j : ℂ) • ContinuousLinearMap.id ℂ (G.baseSpace A) +
            (arcHankelMatrix N i j : ℂ) • G.baseRepresentation A s)) :
    ‖commutator (G.baseOperator A Y) (G.baseRepresentation A s)‖ ≤
      6 * Real.pi ^ 2 * (1 + 4 * cyclicConstant) * ε := by
  sorry

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end
