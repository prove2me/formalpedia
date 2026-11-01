-- Prove2me | Theorems.Thm_OAI_KadisonSimilarity_exists_countable_projection_join_of_equiv
-- name    : OAI.KadisonSimilarity.exists_countable_projection_join_of_equiv
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T08:41:30.79846+00:00
-- url     : https://prove2.me/theorems/0dc39ffc-e58a-434d-88e6-d9ae0235e32b
-- title:
--   OAI.KadisonSimilarity.exists_countable_projection_join_of_equiv: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KadisonSimilarity.similarityTheorem`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KadisonSimilarity.exists_countable_projection_join_of_equiv` of [lean/OAI/Analysis/KadisonSimilarity/Representation/CountableProjectionJoin.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/Representation/CountableProjectionJoin.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KadisonSimilarity`, with `open Generator.Tracial UltrapowerBridge`, `open scoped ComplexOrder`):
--
--   ```lean
--   theorem exists_countable_projection_join_of_equiv
--       {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
--       (M : VonNeumannAlgebra H) (N : VonNeumannAlgebra K)
--       [IsClosed (N.toStarSubalgebra : Set (K →L[ℂ] K))]
--       (e : M.toStarSubalgebra ≃⋆ₐ[ℂ] N.toStarSubalgebra)
--       (υ : TracialRepresentation N)
--       (τ : M.toStarSubalgebra →ₚ[ℂ] ℂ) (σ : N.toStarSubalgebra →ₚ[ℂ] ℂ)
--       (hσ : ∀ b, σ b = υ.trace b) (he : ∀ a, σ (e a) = τ a)
--       (p : ℕ → M.toStarSubalgebra) (hp : ∀ n, IsStarProjection (p n))
--       (C : ℝ) (hC : ∀ n, ∑ i ∈ Finset.range n, (τ (p i)).re ≤ C) :
--       ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ (τ q).re ≤ C ∧
--         (∀ n, q * p n = p n) ∧
--         ∀ r : M.toStarSubalgebra, IsStarProjection r → (∀ n, r * p n = p n) → r * q = q
--   ```
--
--   **Definitions.** The statement is written with `OAI.UltrapowerBridge.TracialRepresentation` and `OAI.UltrapowerBridge.TracialRepresentation.trace` (definitions bundle `OAIQ075A002` of this split); `OAI.KadisonSimilarity.countableJoin_closed` (definitions bundle `OAIQ075A017` of this split).
--
--   **Used by.** The proofs of `OAI.KadisonSimilarity.normal_tracial_cyclic_graph_closable` and `OAI_KadisonSimilarity_projection_tendsto_zero_of_normal_geometry` of this split import it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/Representation/CountableProjectionJoin.lean (declaration OAI.KadisonSimilarity.exists_countable_projection_join_of_equiv)

import Mathlib
import Definitions.Def_OAIQ075A017

section

attribute [-instance] _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace KadisonSimilarity
open Generator.Tracial UltrapowerBridge
open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local instance] OAI.KadisonSimilarity.countableJoin_closed
theorem exists_countable_projection_join_of_equiv
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (M : VonNeumannAlgebra H) (N : VonNeumannAlgebra K)
    [IsClosed (N.toStarSubalgebra : Set (K →L[ℂ] K))]
    (e : M.toStarSubalgebra ≃⋆ₐ[ℂ] N.toStarSubalgebra)
    (υ : TracialRepresentation N)
    (τ : M.toStarSubalgebra →ₚ[ℂ] ℂ) (σ : N.toStarSubalgebra →ₚ[ℂ] ℂ)
    (hσ : ∀ b, σ b = υ.trace b) (he : ∀ a, σ (e a) = τ a)
    (p : ℕ → M.toStarSubalgebra) (hp : ∀ n, IsStarProjection (p n))
    (C : ℝ) (hC : ∀ n, ∑ i ∈ Finset.range n, (τ (p i)).re ≤ C) :
    ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ (τ q).re ≤ C ∧
      (∀ n, q * p n = p n) ∧
      ∀ r : M.toStarSubalgebra, IsStarProjection r → (∀ n, r * p n = p n) → r * q = q := by
  sorry

end KadisonSimilarity

end

end OAI
end
