-- Prove2me | Theorems.Thm_OAI_KadisonSimilarity_finite_standard_bound_of_local_free_corner
-- name    : OAI.KadisonSimilarity.finite_standard_bound_of_local_free_corner
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T08:52:53.588434+00:00
-- url     : https://prove2.me/theorems/d752d74d-64f3-4538-b49f-f772e68e0e51
-- title:
--   OAI.KadisonSimilarity.finite_standard_bound_of_local_free_corner: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KadisonSimilarity.similarityTheorem`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KadisonSimilarity.finite_standard_bound_of_local_free_corner` of [lean/OAI/Analysis/KadisonSimilarity/Tracial/FiniteFactorApplication.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/Tracial/FiniteFactorApplication.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KadisonSimilarity`, with `open HochschildUltrapower`, `open scoped ComplexOrder Topology`):
--
--   ```lean
--   theorem finite_standard_bound_of_local_free_corner
--       (inputs : FiniteFactorFreeCornerInputs τR τB hR hB ω trR trB ρ hρτ hω)
--       (source_normalR : τR.gnsStarAlgHom.range =
--         (representationVonNeumannAlgebra τR.gnsStarAlgHom).toStarSubalgebra)
--       (source_normal : τB.gnsStarAlgHom.range =
--         (representationVonNeumannAlgebra τB.gnsStarAlgHom).toStarSubalgebra)
--       (S : RealTracialSequence τR.toLinearMap)
--       (hsize : Filter.Tendsto (fun j => (Fintype.card (I j) : ℝ)) Filter.atTop Filter.atTop)
--       {r : ℕ} (Y : HilbertCopies τB.GNS r →L[ℂ] HilbertCopies τB.GNS r)
--       {δ : ℝ} (hδ : 0 ≤ δ)
--       (hscalar : ∀ a, ‖commutator Y (amplify (τB.gnsStarAlgHom a) r)‖ ≤ δ * ‖a‖)
--       (h : ℕ) (X : CStarMatrix (Fin h) (Fin h) B) :
--       ‖commutator (amplify Y h)
--         (representedMatrix (amplifiedScalarRepresentation τB.gnsStarAlgHom r) X)‖ ≤
--         (3 * cornerConstant + 2) * δ * ‖X‖
--   ```
--
--   **Definitions.** The statement is written with `OAI.KadisonSimilarity.NestedTracialMatrices`, `OAI.KadisonSimilarity.gnsTracialVector` and `OAI.KadisonSimilarity.representedMatrix` (definitions bundle `OAIQ075A004` of this split); `OAI.KadisonSimilarity.RealTracialSequence` and `OAI.KadisonSimilarity.representationVonNeumannAlgebra` (definitions bundle `OAIQ075A005` of this split); `OAI.KadisonSimilarity.FiniteFactorFreeCornerInputs` and `OAI.KadisonSimilarity.amplifiedScalarRepresentation` (definitions bundle `OAIQ075A023` of this split); `OAI.KadisonSimilarity.HilbertCopies`, `OAI.KadisonSimilarity.amplify`, `OAI.KadisonSimilarity.commutator` and `OAI.KadisonSimilarity.cornerConstant` (the published bundle `Def_KadisonSimilarity`).
--
--   **Used by.** The proof of `OAI.KadisonSimilarity.FiniteFactorModel.estimate` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/Tracial/FiniteFactorApplication.lean (declaration OAI.KadisonSimilarity.finite_standard_bound_of_local_free_corner)

import Mathlib
import Definitions.Def_KadisonSimilarity
import Definitions.Def_OAIQ075A023

section

attribute [-instance] _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace KadisonSimilarity
open HochschildUltrapower
open scoped ComplexOrder Topology

variable {R B : Type*} [CStarAlgebra R] [CStarAlgebra B]
  [PartialOrder R] [StarOrderedRing R] [PartialOrder B] [StarOrderedRing B]
  (τR : R →ₚ[ℂ] ℂ) (τB : B →ₚ[ℂ] ℂ)
  (hR : τR 1 = 1) (hB : τB 1 = 1) (ω : Ultrafilter ℕ)
  (trR : ∀ a b : R, τR (a * b) = τR (b * a))
  (trB : ∀ a b : B, τB (a * b) = τB (b * a))
  (ρ : R →⋆ₐ[ℂ] B) (hρτ : ∀ a, τB (ρ a) = τR a)
  (hfR : ∀ a : R, τR (star a * a) = 0 → a = 0)
  (hfB : ∀ a : B, τB (star a * a) = 0 → a = 0)
  {I : ℕ → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Nonempty (I j)]
  (M : NestedTracialMatrices (A := I) τR.toLinearMap (gnsTracialVector τR))

variable (hω : (ω : Filter ℕ) ≤ Filter.cofinite)

include hfR hfB M in
theorem finite_standard_bound_of_local_free_corner
    (inputs : FiniteFactorFreeCornerInputs τR τB hR hB ω trR trB ρ hρτ hω)
    (source_normalR : τR.gnsStarAlgHom.range =
      (representationVonNeumannAlgebra τR.gnsStarAlgHom).toStarSubalgebra)
    (source_normal : τB.gnsStarAlgHom.range =
      (representationVonNeumannAlgebra τB.gnsStarAlgHom).toStarSubalgebra)
    (S : RealTracialSequence τR.toLinearMap)
    (hsize : Filter.Tendsto (fun j => (Fintype.card (I j) : ℝ)) Filter.atTop Filter.atTop)
    {r : ℕ} (Y : HilbertCopies τB.GNS r →L[ℂ] HilbertCopies τB.GNS r)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hscalar : ∀ a, ‖commutator Y (amplify (τB.gnsStarAlgHom a) r)‖ ≤ δ * ‖a‖)
    (h : ℕ) (X : CStarMatrix (Fin h) (Fin h) B) :
    ‖commutator (amplify Y h)
      (representedMatrix (amplifiedScalarRepresentation τB.gnsStarAlgHom r) X)‖ ≤
      (3 * cornerConstant + 2) * δ * ‖X‖ := by
  sorry

end KadisonSimilarity

end

end OAI
end
