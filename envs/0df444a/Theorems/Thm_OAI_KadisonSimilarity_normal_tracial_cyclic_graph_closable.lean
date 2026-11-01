-- Prove2me | Theorems.Thm_OAI_KadisonSimilarity_normal_tracial_cyclic_graph_closable
-- name    : OAI.KadisonSimilarity.normal_tracial_cyclic_graph_closable
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T08:46:30.263745+00:00
-- url     : https://prove2.me/theorems/29dcf607-7c15-4ff1-9b07-19f432097cc7
-- title:
--   OAI.KadisonSimilarity.normal_tracial_cyclic_graph_closable: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KadisonSimilarity.similarityTheorem`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KadisonSimilarity.normal_tracial_cyclic_graph_closable` of [lean/OAI/Analysis/KadisonSimilarity/Derivation/NormalCyclicGraph.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/Derivation/NormalCyclicGraph.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KadisonSimilarity`, with `open Filter`, `open scoped Topology ComplexOrder`):
--
--   ```lean
--   theorem normal_tracial_cyclic_graph_closable
--       (M : VonNeumannAlgebra H) (G : TracialCornerGeometry M.toStarSubalgebra E)
--       (τ : M.toStarSubalgebra →ₚ[ℂ] ℂ) (hτ : ∀ a, τ a = G.trace a)
--       (h1 : G.trace 1 = 1) (hf : Function.Injective G.vector)
--       (N : VonNeumannAlgebra E) (hN : G.left.range = N.toStarSubalgebra)
--       (ρ : M.toStarSubalgebra →⋆ₐ[ℂ] (K →L[ℂ] K)) (J : K →ₗᵢ[ℂ] H)
--       (hJ : ∀ a, J.toContinuousLinearMap.comp (ρ a) =
--         (a : H →L[ℂ] H).comp J.toContinuousLinearMap) (ξ : K)
--       (x : cyclicGraph G.left ρ (G.vector 1) ξ)
--       (hx : (x : RectangularSum E K).fst = 0) :
--       (x : RectangularSum E K).snd = 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.KadisonSimilarity.RectangularSum` and `OAI.KadisonSimilarity.TracialCornerGeometry` (definitions bundle `OAIQ075A004` of this split); `OAI.KadisonSimilarity.normalCyclic_closed` (definitions bundle `OAIQ075A006` of this split); `OAI.KadisonSimilarity.cyclicGraph` (definitions bundle `OAIQ075A017` of this split).
--
--   **Used by.** The proof of `OAI.KadisonSimilarity.FiniteFactorModel.estimate` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/Derivation/NormalCyclicGraph.lean (declaration OAI.KadisonSimilarity.normal_tracial_cyclic_graph_closable)

import Mathlib
import Definitions.Def_OAIQ075A017

section

attribute [-instance] _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace KadisonSimilarity
open Filter
open scoped Topology ComplexOrder

variable {H K E : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

attribute [local instance] OAI.KadisonSimilarity.normalCyclic_closed
theorem normal_tracial_cyclic_graph_closable
    (M : VonNeumannAlgebra H) (G : TracialCornerGeometry M.toStarSubalgebra E)
    (τ : M.toStarSubalgebra →ₚ[ℂ] ℂ) (hτ : ∀ a, τ a = G.trace a)
    (h1 : G.trace 1 = 1) (hf : Function.Injective G.vector)
    (N : VonNeumannAlgebra E) (hN : G.left.range = N.toStarSubalgebra)
    (ρ : M.toStarSubalgebra →⋆ₐ[ℂ] (K →L[ℂ] K)) (J : K →ₗᵢ[ℂ] H)
    (hJ : ∀ a, J.toContinuousLinearMap.comp (ρ a) =
      (a : H →L[ℂ] H).comp J.toContinuousLinearMap) (ξ : K)
    (x : cyclicGraph G.left ρ (G.vector 1) ξ)
    (hx : (x : RectangularSum E K).fst = 0) :
    (x : RectangularSum E K).snd = 0 := by
  sorry

end KadisonSimilarity

end

end OAI
end
