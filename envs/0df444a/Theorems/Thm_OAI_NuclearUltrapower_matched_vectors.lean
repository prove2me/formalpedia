-- Prove2me | Theorems.Thm_OAI_NuclearUltrapower_matched_vectors
-- name    : OAI.NuclearUltrapower.matched_vectors
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T07:14:46.64104+00:00
-- url     : https://prove2.me/theorems/702a47a4-e28b-43c7-a48b-2719ffe7cf4d
-- title:
--   OAI.NuclearUltrapower.matched_vectors: intermediate lemma from OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.NuclearUltrapower.main_no_embedding`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)*, OpenAI Math Release, September 23, 2026, result family 292, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.NuclearUltrapower.matched_vectors` of [lean/OAI/Analysis/NuclearUltrapower/PullbackMatching.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/PullbackMatching.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.NuclearUltrapower`, with `open Filter`, `open scoped Topology InnerProductSpace`):
--
--   ```lean
--   theorem matched_vectors (κ a : ℝ) (hgap : HasKazhdanGap.{u,v} S κ)
--       (hS : Subgroup.closure (S : Set Γ) = ⊤) (ha : a < κ)
--       (hω : ∀ n : ℕ, ({n} : Set ℕ) ∉ (ω : Filter ℕ))
--       (h1 : ∀ n, u 1 n = 1)
--       (hmul : ∀ g h, Tendsto (fun n => ‖(u (g*h) n : B) - (u g n : B)*(u h n : B)‖)
--         (ω : Filter ℕ) (𝓝 0))
--       (hm : ∀ᶠ n in (ω : Filter ℕ), Matches ρ S (fun g => u g n) a (π n)) :
--       ∃ ξ : ∀ n, TensorHilbert E (π n), (∀ n, ‖ξ n‖ = 1) ∧
--         ∀ g, Tendsto (fun n => ‖matchingTuple ρ (fun g => u g n) (π n) g (ξ n) - ξ n‖)
--           (ω : Filter ℕ) (𝓝 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.NuclearUltrapower.TensorHilbert` (definitions bundle `OAIQ019N000` of this split); `OAI.NuclearUltrapower.FiniteUnitaryRep` (definitions bundle `OAIQ019N001` of this split); `OAI.NuclearUltrapower.HasKazhdanGap` (definitions bundle `OAIQ019N002` of this split); `OAI.NuclearUltrapower.Matches` (definitions bundle `OAIQ019N043` of this split); `OAI.NuclearUltrapower.matchingTuple` (definitions bundle `OAIQ019N046` of this split).
--
--   **Used by.** The proof of `OAI.NuclearUltrapower.uniform_predecessors` of this split imports it.
-- source:
--   OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 292; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/NuclearUltrapower.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/PullbackMatching.lean (declaration OAI.NuclearUltrapower.matched_vectors)

import Mathlib
import Definitions.Def_OAIQ019N043

section

attribute [-instance] _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Filter
open scoped Topology InnerProductSpace
namespace NuclearUltrapower
universe u v
section MatchedVectors
variable {Γ : Type u} [Group Γ] {B E : Type v} [CStarAlgebra B]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [Nontrivial E]
  (ρ : B →⋆ₐ[ℂ] (E →L[ℂ] E)) (S : Finset Γ) (u : Γ → ℕ → unitary B)
  (π : ℕ → FiniteUnitaryRep.{u,v} Γ) (ω : Ultrafilter ℕ)

theorem matched_vectors (κ a : ℝ) (hgap : HasKazhdanGap.{u,v} S κ)
    (hS : Subgroup.closure (S : Set Γ) = ⊤) (ha : a < κ)
    (hω : ∀ n : ℕ, ({n} : Set ℕ) ∉ (ω : Filter ℕ))
    (h1 : ∀ n, u 1 n = 1)
    (hmul : ∀ g h, Tendsto (fun n => ‖(u (g*h) n : B) - (u g n : B)*(u h n : B)‖)
      (ω : Filter ℕ) (𝓝 0))
    (hm : ∀ᶠ n in (ω : Filter ℕ), Matches ρ S (fun g => u g n) a (π n)) :
    ∃ ξ : ∀ n, TensorHilbert E (π n), (∀ n, ‖ξ n‖ = 1) ∧
      ∀ g, Tendsto (fun n => ‖matchingTuple ρ (fun g => u g n) (π n) g (ξ n) - ξ n‖)
        (ω : Filter ℕ) (𝓝 0) := by
  sorry
end MatchedVectors
end NuclearUltrapower
end
end

end OAI
end
