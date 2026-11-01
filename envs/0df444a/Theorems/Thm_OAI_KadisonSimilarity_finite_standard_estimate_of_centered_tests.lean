-- Prove2me | Theorems.Thm_OAI_KadisonSimilarity_finite_standard_estimate_of_centered_tests
-- name    : OAI.KadisonSimilarity.finite_standard_estimate_of_centered_tests
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T09:14:21.268608+00:00
-- url     : https://prove2.me/theorems/c5a05065-a1cc-43e7-93d5-e09c37d0b597
-- title:
--   OAI.KadisonSimilarity.finite_standard_estimate_of_centered_tests: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KadisonSimilarity.similarityTheorem`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KadisonSimilarity.finite_standard_estimate_of_centered_tests` of [lean/OAI/Analysis/KadisonSimilarity/Representation/FiniteStandardEstimate.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/Representation/FiniteStandardEstimate.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KadisonSimilarity`, with `open scoped ComplexOrder`):
--
--   ```lean
--   theorem finite_standard_estimate_of_centered_tests
--       (τ : A →ₚ[ℂ] ℂ)
--       (F : ∀ j, Matrix (I j) (I j) ℂ →⋆ₐ[ℂ] A)
--       (transition : ∀ j k, j ≤ k →
--         Matrix (I j) (I j) ℂ →⋆ₐ[ℂ] Matrix (I k) (I k) ℂ)
--       (hcompat : ∀ j k h a, F k (transition j k h a) = F j a)
--       {c : ℝ} (hc : 0 ≤ c)
--       (hcentered : ∀ (m : ℕ) [NeZero m]
--         (Y₀ : HilbertCopies τ.GNS (4 * m) →L[ℂ] HilbertCopies τ.GNS (4 * m))
--         (δ : ℝ), 0 ≤ δ →
--         (∀ a, ‖commutator Y₀ (amplify (τ.gnsStarAlgHom a) (4 * m))‖ ≤
--           (3 * δ) * ‖a‖) →
--         (∀ j a, commutator Y₀ (amplify (τ.gnsStarAlgHom (F j a)) (4 * m)) = 0) →
--         ∀ S : CStarMatrix (Fin (4 * m)) (Fin (4 * m)) A,
--           star S = S → S * S = 1 → normalizedMatrixTrace τ (4 * m) S = 0 →
--           ‖commutator (matrixGNSLiftOperator τ Y₀)
--             ((normalizedMatrixTrace τ (4 * m)).gnsStarAlgHom S)‖ ≤ c * (3 * δ))
--       {r : ℕ} (Y : HilbertCopies τ.GNS r →L[ℂ] HilbertCopies τ.GNS r)
--       {δ : ℝ} (hδ : 0 ≤ δ)
--       (hscalar : ∀ a, ‖commutator Y (amplify (τ.gnsStarAlgHom a) r)‖ ≤ δ * ‖a‖)
--       (h : ℕ) (X : CStarMatrix (Fin h) (Fin h) A) :
--       ‖commutator (amplify Y h)
--         (representedMatrix (amplifiedScalarRepresentation τ.gnsStarAlgHom r) X)‖ ≤
--         (3 * c + 2) * δ * ‖X‖
--   ```
--
--   **Definitions.** The statement is written with `OAI.KadisonSimilarity.normalizedMatrixTrace` and `OAI.KadisonSimilarity.representedMatrix` (definitions bundle `OAIQ075A004` of this split); `OAI.KadisonSimilarity.amplifiedScalarRepresentation` (definitions bundle `OAIQ075A023` of this split); `OAI.KadisonSimilarity.matrixGNSLiftOperator` (definitions bundle `OAIQ075A030` of this split); `OAI.KadisonSimilarity.HilbertCopies`, `OAI.KadisonSimilarity.amplify` and `OAI.KadisonSimilarity.commutator` (the published bundle `Def_KadisonSimilarity`).
--
--   **Used by.** The proof of `OAI.KadisonSimilarity.finite_standard_bound_of_local_free_corner` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/Representation/FiniteStandardEstimate.lean (declaration OAI.KadisonSimilarity.finite_standard_estimate_of_centered_tests)

import Mathlib
import Definitions.Def_KadisonSimilarity
import Definitions.Def_OAIQ075A030

section

attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace KadisonSimilarity

open scoped ComplexOrder

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {I : ℕ → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Nonempty (I j)]

theorem finite_standard_estimate_of_centered_tests
    (τ : A →ₚ[ℂ] ℂ)
    (F : ∀ j, Matrix (I j) (I j) ℂ →⋆ₐ[ℂ] A)
    (transition : ∀ j k, j ≤ k →
      Matrix (I j) (I j) ℂ →⋆ₐ[ℂ] Matrix (I k) (I k) ℂ)
    (hcompat : ∀ j k h a, F k (transition j k h a) = F j a)
    {c : ℝ} (hc : 0 ≤ c)
    (hcentered : ∀ (m : ℕ) [NeZero m]
      (Y₀ : HilbertCopies τ.GNS (4 * m) →L[ℂ] HilbertCopies τ.GNS (4 * m))
      (δ : ℝ), 0 ≤ δ →
      (∀ a, ‖commutator Y₀ (amplify (τ.gnsStarAlgHom a) (4 * m))‖ ≤
        (3 * δ) * ‖a‖) →
      (∀ j a, commutator Y₀ (amplify (τ.gnsStarAlgHom (F j a)) (4 * m)) = 0) →
      ∀ S : CStarMatrix (Fin (4 * m)) (Fin (4 * m)) A,
        star S = S → S * S = 1 → normalizedMatrixTrace τ (4 * m) S = 0 →
        ‖commutator (matrixGNSLiftOperator τ Y₀)
          ((normalizedMatrixTrace τ (4 * m)).gnsStarAlgHom S)‖ ≤ c * (3 * δ))
    {r : ℕ} (Y : HilbertCopies τ.GNS r →L[ℂ] HilbertCopies τ.GNS r)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hscalar : ∀ a, ‖commutator Y (amplify (τ.gnsStarAlgHom a) r)‖ ≤ δ * ‖a‖)
    (h : ℕ) (X : CStarMatrix (Fin h) (Fin h) A) :
    ‖commutator (amplify Y h)
      (representedMatrix (amplifiedScalarRepresentation τ.gnsStarAlgHom r) X)‖ ≤
      (3 * c + 2) * δ * ‖X‖ := by
  sorry

end KadisonSimilarity

end

end OAI
end
