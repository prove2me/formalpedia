-- Prove2me | Theorems.Thm_OAI_KadisonSimilarity_free_corner_from_multiplicity_propagation
-- name    : OAI.KadisonSimilarity.free_corner_from_multiplicity_propagation
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-03T16:41:57.624446+00:00
-- url     : https://prove2.me/theorems/0ff9a86b-5812-4548-b039-07d5ca99be5f
-- title:
--   OAI.KadisonSimilarity.free_corner_from_multiplicity_propagation: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KadisonSimilarity.similarityTheorem`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KadisonSimilarity.free_corner_from_multiplicity_propagation` of [lean/OAI/Analysis/KadisonSimilarity/FreeProduct/WordPropagationTransfer.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/FreeProduct/WordPropagationTransfer.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KadisonSimilarity`):
--
--   ```lean
--   theorem free_corner_from_multiplicity_propagation
--       {N : ℕ} (hN : 0 < N) (R : ∀ n, K →ₗᵢ[ℂ] J n)
--       (d : E) (r : F) (hd : ‖d‖ = 1) (hr : ‖r‖ = 1)
--       (Y T : H →L[ℂ] H) (B S : K →L[ℂ] K) (Bn : ∀ n, J n →L[ℂ] J n)
--       (hY : ∀ n v, Y (U.inclusion n (hilbertTensorInsert v
--           (endpointWord d (fun _ : Fin n => r)))) =
--         U.inclusion n (hilbertTensorInsert (Bn n v)
--           (endpointWord d (fun _ : Fin n => r))))
--       (hYstar : ∀ n v, Y.adjoint (U.inclusion n (hilbertTensorInsert v
--           (endpointWord d (fun _ : Fin n => r)))) =
--         U.inclusion n (hilbertTensorInsert ((Bn n).adjoint v)
--           (endpointWord d (fun _ : Fin n => r))))
--       (hlevel : ∀ n x, Y (U.inclusion n x) ∈ (U.inclusion n).toLinearMap.range)
--       (hlevelstar : ∀ n x, Y.adjoint (U.inclusion n x) ∈ (U.inclusion n).toLinearMap.range)
--       (toeplitz : Matrix (Fin N) (Fin N) ℝ)
--       {u ε c₀ : ℝ} (hu : 0 < u) (hε : 0 ≤ ε) (hc₀ : 0 ≤ c₀)
--       (hT : ‖T‖ ≤ 3 * u) (hcomm : ‖commutator Y T‖ ≤ ε * ‖T‖)
--       (hprop : ∀ n x, ‖Bn n (R n x) - R n (B x)‖ ≤ 2 * c₀ * ε * ‖x‖)
--       (hpropstar : ∀ n x, ‖(Bn n).adjoint (R n x) - R n (B.adjoint x)‖ ≤
--         2 * c₀ * ε * ‖x‖)
--       (hfourier :
--         let V : Fin N → K →L[ℂ] H := fun i =>
--           (repeatedWordInclusion U i.val (R i.val) d r hd hr).toContinuousLinearMap
--         (sumColumns V).adjoint.comp (T.comp (sumColumns V)) =
--           (u : ℂ) • matrixOperator (fun i j =>
--             (toeplitz i j : ℂ) • ContinuousLinearMap.id ℂ K +
--               (arcHankelMatrix N i j : ℂ) • S)) :
--       ‖commutator B S‖ ≤ 6 * Real.pi ^ 2 * (1 + 4 * c₀) * ε
--   ```
--
--   **Definitions.** The statement is written with `OAI.KadisonSimilarity.CompletedTensorWord`, `OAI.KadisonSimilarity.HilbertTensor`, `OAI.KadisonSimilarity.OrthogonalWordLevels`, `OAI.KadisonSimilarity.TensorWord`, `OAI.KadisonSimilarity.hilbertTensorInnerProductSpace`, `OAI.KadisonSimilarity.hilbertTensorNormedAddCommGroup`, `OAI.KadisonSimilarity.sumColumns`, `OAI.KadisonSimilarity.tensorWordSpace` and `OAI.KadisonSimilarity.TensorWordSpace` (definitions bundle `OAIQ075A004` of this split); `OAI.KadisonSimilarity.arcHankelMatrix` (definitions bundle `OAIQ075A006` of this split); `OAI.KadisonSimilarity.EndpointTensor` and `OAI.KadisonSimilarity.endpointWord` (definitions bundle `OAIQ075A009` of this split); `OAI.KadisonSimilarity.MultiplicityWordSpace`, `OAI.KadisonSimilarity.hilbertTensorInsert` and `OAI.KadisonSimilarity.repeatedWordInclusion` (definitions bundle `OAIQ075A016` of this split); `OAI.KadisonSimilarity.HilbertCopies`, `OAI.KadisonSimilarity.commutator` and `OAI.KadisonSimilarity.matrixOperator` (the published bundle `Def_KadisonSimilarity`).
--
--   **Used by.** The proof of `OAI.KadisonSimilarity.TracialCornerGeometry.free_corner_estimate_of_published_words` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/FreeProduct/WordPropagationTransfer.lean (declaration OAI.KadisonSimilarity.free_corner_from_multiplicity_propagation)

import Mathlib
import Definitions.Def_KadisonSimilarity
import Definitions.Def_OAIQ075A006
import Definitions.Def_OAIQ075A016

section

attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace KadisonSimilarity

universe u
variable {E F : Type u} {K H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {J : ℕ → Type*} [∀ n, NormedAddCommGroup (J n)]
  [∀ n, InnerProductSpace ℂ (J n)] [∀ n, CompleteSpace (J n)]

variable (U : OrthogonalWordLevels (MultiplicityWordSpace J E F) H)

theorem free_corner_from_multiplicity_propagation
    {N : ℕ} (hN : 0 < N) (R : ∀ n, K →ₗᵢ[ℂ] J n)
    (d : E) (r : F) (hd : ‖d‖ = 1) (hr : ‖r‖ = 1)
    (Y T : H →L[ℂ] H) (B S : K →L[ℂ] K) (Bn : ∀ n, J n →L[ℂ] J n)
    (hY : ∀ n v, Y (U.inclusion n (hilbertTensorInsert v
        (endpointWord d (fun _ : Fin n => r)))) =
      U.inclusion n (hilbertTensorInsert (Bn n v)
        (endpointWord d (fun _ : Fin n => r))))
    (hYstar : ∀ n v, Y.adjoint (U.inclusion n (hilbertTensorInsert v
        (endpointWord d (fun _ : Fin n => r)))) =
      U.inclusion n (hilbertTensorInsert ((Bn n).adjoint v)
        (endpointWord d (fun _ : Fin n => r))))
    (hlevel : ∀ n x, Y (U.inclusion n x) ∈ (U.inclusion n).toLinearMap.range)
    (hlevelstar : ∀ n x, Y.adjoint (U.inclusion n x) ∈ (U.inclusion n).toLinearMap.range)
    (toeplitz : Matrix (Fin N) (Fin N) ℝ)
    {u ε c₀ : ℝ} (hu : 0 < u) (hε : 0 ≤ ε) (hc₀ : 0 ≤ c₀)
    (hT : ‖T‖ ≤ 3 * u) (hcomm : ‖commutator Y T‖ ≤ ε * ‖T‖)
    (hprop : ∀ n x, ‖Bn n (R n x) - R n (B x)‖ ≤ 2 * c₀ * ε * ‖x‖)
    (hpropstar : ∀ n x, ‖(Bn n).adjoint (R n x) - R n (B.adjoint x)‖ ≤
      2 * c₀ * ε * ‖x‖)
    (hfourier :
      let V : Fin N → K →L[ℂ] H := fun i =>
        (repeatedWordInclusion U i.val (R i.val) d r hd hr).toContinuousLinearMap
      (sumColumns V).adjoint.comp (T.comp (sumColumns V)) =
        (u : ℂ) • matrixOperator (fun i j =>
          (toeplitz i j : ℂ) • ContinuousLinearMap.id ℂ K +
            (arcHankelMatrix N i j : ℂ) • S)) :
    ‖commutator B S‖ ≤ 6 * Real.pi ^ 2 * (1 + 4 * c₀) * ε := by
  sorry

end KadisonSimilarity

end

end OAI
end
