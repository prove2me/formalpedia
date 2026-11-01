-- Prove2me | Theorems.Thm_OAI_KadisonSimilarity_TracialCornerGeometry_commutator_bound_of_actual_dihedral_compression
-- name    : OAI.KadisonSimilarity.TracialCornerGeometry.commutator_bound_of_actual_dihedral_compression
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-31T08:47:09.396551+00:00
-- url     : https://prove2.me/theorems/d525aecb-4903-4c8a-9022-d242964a1c4e
-- title:
--   OAI.KadisonSimilarity.TracialCornerGeometry.commutator_bound_of_actual_dihedral_compression (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KadisonSimilarity.similarityTheorem`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KadisonSimilarity.TracialCornerGeometry.commutator_bound_of_actual_dihedral_compression` of [lean/OAI/Analysis/KadisonSimilarity/FreeProduct/TracialDihedralEndgame.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/FreeProduct/TracialDihedralEndgame.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KadisonSimilarity.TracialCornerGeometry`):
--
--   ```lean
--   theorem commutator_bound_of_actual_dihedral_compression
--       (hτ : G.trace 1 = 1) (hf : ScalarFree G.trace D A)
--       (d : D) (s : A) (e : D)
--       (hdstar : star d = d) (hdsq : d * d = 1) (hd0 : G.trace (d : P) = 0)
--       (hsstar : star s = s) (hssq : s * s = 1) (hs0 : G.trace (s : P) = 0)
--       (he : IsStarProjection e) {t : ℝ} (ht : 0 < t) (hte : G.trace (e : P) = (t : ℂ))
--       (U : OrthogonalWordLevels
--         (MultiplicityWordSpace (WordMultiplicity (G.baseVector A 1)) (G.baseSpace D)
--           (centeredSubspace (G.baseVector D 1))) H)
--       (hU : TracialWordFormula G A D U)
--       (Y T : H →L[ℂ] H)
--       (B : ∀ n, WordMultiplicity (G.baseVector A 1) n →L[ℂ]
--         WordMultiplicity (G.baseVector A 1) n)
--       (hY : ∀ n v d' r, Y (U.inclusion n
--           (hilbertTensorInsert v (endpointWord d' (fun _ : Fin n => r)))) =
--         U.inclusion n (hilbertTensorInsert (B n v) (endpointWord d' (fun _ : Fin n => r))))
--       (hYstar : ∀ n v d' r, Y.adjoint (U.inclusion n
--           (hilbertTensorInsert v (endpointWord d' (fun _ : Fin n => r)))) =
--         U.inclusion n (hilbertTensorInsert ((B n).adjoint v)
--           (endpointWord d' (fun _ : Fin n => r))))
--       (hlevel : ∀ n x, Y (U.inclusion n x) ∈ (U.inclusion n).toLinearMap.range)
--       (hlevelstar : ∀ n x, Y.adjoint (U.inclusion n x) ∈ (U.inclusion n).toLinearMap.range)
--       {N : ℕ} (hN : 0 < N) (toeplitz : Matrix (Fin N) (Fin N) ℝ)
--       {u ε c₀ : ℝ} (hu : 0 < u) (hε : 0 ≤ ε) (hc₀ : 0 ≤ c₀)
--       (hT : ‖T‖ ≤ 3 * u) (hcomm : ‖commutator Y T‖ ≤ ε * ‖T‖)
--       (hprop : ∀ n v,
--         ‖B n (G.baseSymmetryRepeatedInclusion A s hs0 hsstar hssq hτ n v) -
--           G.baseSymmetryRepeatedInclusion A s hs0 hsstar hssq hτ n
--             (G.baseOperator A Y v)‖ ≤ 2 * c₀ * ε * ‖v‖)
--       (hpropstar : ∀ n v,
--         ‖(B n).adjoint (G.baseSymmetryRepeatedInclusion A s hs0 hsstar hssq hτ n v) -
--           G.baseSymmetryRepeatedInclusion A s hs0 hsstar hssq hτ n
--             ((G.baseOperator A Y).adjoint v)‖ ≤ 2 * c₀ * ε * ‖v‖)
--       (hfourier :
--         let V := G.tracialDihedralColumns D A hf hτ d s e hdstar hdsq hd0 hsstar hssq hs0
--           he ht hte N
--         (sumColumns V).adjoint.comp (T.comp (sumColumns V)) =
--           (u : ℂ) • matrixOperator (fun i j =>
--             (toeplitz i j : ℂ) • ContinuousLinearMap.id ℂ (G.baseSpace A) +
--               (arcHankelMatrix N i j : ℂ) • G.baseRepresentation A s)) :
--       ‖commutator (G.baseOperator A Y) (G.baseRepresentation A s)‖ ≤
--         6 * Real.pi ^ 2 * (1 + 4 * c₀) * ε
--   ```
--
--   **Definitions.** The statement is written with `OAI.closedSubmoduleInner`, `OAI.closedSubmoduleNormedAddCommGroup`, `OAI.closedSubmoduleNormedSpace`, `OAI.KadisonSimilarity.CompletedTensorWord`, `OAI.KadisonSimilarity.HilbertTensor`, `OAI.KadisonSimilarity.OrthogonalWordLevels`, `OAI.KadisonSimilarity.ScalarFree`, `OAI.KadisonSimilarity.TensorWord`, `OAI.KadisonSimilarity.TracialCornerGeometry`, `OAI.KadisonSimilarity.centeredSubspace`, `OAI.KadisonSimilarity.hilbertTensorCompleteSpace`, `OAI.KadisonSimilarity.hilbertTensorInnerProductSpace`, `OAI.KadisonSimilarity.hilbertTensorNormedAddCommGroup`, `OAI.KadisonSimilarity.sumColumns`, `OAI.KadisonSimilarity.tensorWordSpace` and `OAI.KadisonSimilarity.TensorWordSpace` (definitions bundle `OAIQ075A004` of this split); `OAI.KadisonSimilarity.arcHankelMatrix` (definitions bundle `OAIQ075A006` of this split); `OAI.KadisonSimilarity.EndpointTensor` and `OAI.KadisonSimilarity.endpointWord` (definitions bundle `OAIQ075A009` of this split); `OAI.KadisonSimilarity.MultiplicityWordSpace`, `OAI.KadisonSimilarity.WordMultiplicity`, `OAI.KadisonSimilarity.hilbertTensorInsert`, `OAI.KadisonSimilarity.TracialCornerGeometry.baseOperator`, `OAI.KadisonSimilarity.TracialCornerGeometry.baseRepresentation`, `OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace`, `OAI.KadisonSimilarity.TracialCornerGeometry.baseVector`, `OAI.KadisonSimilarity.TracialCornerGeometry.dihedralMultiplicityInnerFamily` and `OAI.KadisonSimilarity.TracialCornerGeometry.dihedralMultiplicityNormedFamily` (definitions bundle `OAIQ075A016` of this split); `OAI.KadisonSimilarity.TracialWordFormula`, `OAI.KadisonSimilarity.TracialCornerGeometry.baseSymmetryRepeatedInclusion` and `OAI.KadisonSimilarity.TracialCornerGeometry.tracialDihedralColumns` (definitions bundle `OAIQ075A024` of this split); `OAI.KadisonSimilarity.HilbertCopies`, `OAI.KadisonSimilarity.commutator` and `OAI.KadisonSimilarity.matrixOperator` (the published bundle `Def_KadisonSimilarity`).
--
--   **Used by.** The proof of `OAI.KadisonSimilarity.TracialCornerGeometry.free_corner_estimate_of_published_words` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/FreeProduct/TracialDihedralEndgame.lean (declaration OAI.KadisonSimilarity.TracialCornerGeometry.commutator_bound_of_actual_dihedral_compression)

import Mathlib
import Definitions.Def_KadisonSimilarity
import Definitions.Def_OAIQ075A024

section

attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace KadisonSimilarity

attribute [local irreducible] TracialCornerGeometry.baseSpace tensorWordSpace

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]

attribute [local instance] dihedralMultiplicityNormedFamily dihedralMultiplicityInnerFamily

theorem commutator_bound_of_actual_dihedral_compression
    (hτ : G.trace 1 = 1) (hf : ScalarFree G.trace D A)
    (d : D) (s : A) (e : D)
    (hdstar : star d = d) (hdsq : d * d = 1) (hd0 : G.trace (d : P) = 0)
    (hsstar : star s = s) (hssq : s * s = 1) (hs0 : G.trace (s : P) = 0)
    (he : IsStarProjection e) {t : ℝ} (ht : 0 < t) (hte : G.trace (e : P) = (t : ℂ))
    (U : OrthogonalWordLevels
      (MultiplicityWordSpace (WordMultiplicity (G.baseVector A 1)) (G.baseSpace D)
        (centeredSubspace (G.baseVector D 1))) H)
    (hU : TracialWordFormula G A D U)
    (Y T : H →L[ℂ] H)
    (B : ∀ n, WordMultiplicity (G.baseVector A 1) n →L[ℂ]
      WordMultiplicity (G.baseVector A 1) n)
    (hY : ∀ n v d' r, Y (U.inclusion n
        (hilbertTensorInsert v (endpointWord d' (fun _ : Fin n => r)))) =
      U.inclusion n (hilbertTensorInsert (B n v) (endpointWord d' (fun _ : Fin n => r))))
    (hYstar : ∀ n v d' r, Y.adjoint (U.inclusion n
        (hilbertTensorInsert v (endpointWord d' (fun _ : Fin n => r)))) =
      U.inclusion n (hilbertTensorInsert ((B n).adjoint v)
        (endpointWord d' (fun _ : Fin n => r))))
    (hlevel : ∀ n x, Y (U.inclusion n x) ∈ (U.inclusion n).toLinearMap.range)
    (hlevelstar : ∀ n x, Y.adjoint (U.inclusion n x) ∈ (U.inclusion n).toLinearMap.range)
    {N : ℕ} (hN : 0 < N) (toeplitz : Matrix (Fin N) (Fin N) ℝ)
    {u ε c₀ : ℝ} (hu : 0 < u) (hε : 0 ≤ ε) (hc₀ : 0 ≤ c₀)
    (hT : ‖T‖ ≤ 3 * u) (hcomm : ‖commutator Y T‖ ≤ ε * ‖T‖)
    (hprop : ∀ n v,
      ‖B n (G.baseSymmetryRepeatedInclusion A s hs0 hsstar hssq hτ n v) -
        G.baseSymmetryRepeatedInclusion A s hs0 hsstar hssq hτ n
          (G.baseOperator A Y v)‖ ≤ 2 * c₀ * ε * ‖v‖)
    (hpropstar : ∀ n v,
      ‖(B n).adjoint (G.baseSymmetryRepeatedInclusion A s hs0 hsstar hssq hτ n v) -
        G.baseSymmetryRepeatedInclusion A s hs0 hsstar hssq hτ n
          ((G.baseOperator A Y).adjoint v)‖ ≤ 2 * c₀ * ε * ‖v‖)
    (hfourier :
      let V := G.tracialDihedralColumns D A hf hτ d s e hdstar hdsq hd0 hsstar hssq hs0
        he ht hte N
      (sumColumns V).adjoint.comp (T.comp (sumColumns V)) =
        (u : ℂ) • matrixOperator (fun i j =>
          (toeplitz i j : ℂ) • ContinuousLinearMap.id ℂ (G.baseSpace A) +
            (arcHankelMatrix N i j : ℂ) • G.baseRepresentation A s)) :
    ‖commutator (G.baseOperator A Y) (G.baseRepresentation A s)‖ ≤
      6 * Real.pi ^ 2 * (1 + 4 * c₀) * ε := by
  sorry

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end
