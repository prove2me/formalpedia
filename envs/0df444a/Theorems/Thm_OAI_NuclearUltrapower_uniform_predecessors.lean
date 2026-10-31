-- Prove2me | Theorems.Thm_OAI_NuclearUltrapower_uniform_predecessors
-- name    : OAI.NuclearUltrapower.uniform_predecessors
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T07:11:47.532465+00:00
-- url     : https://prove2.me/theorems/1538ef4d-1f87-4ee6-880b-dffb0c28fbf2
-- title:
--   OAI.NuclearUltrapower.uniform_predecessors: intermediate lemma from OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.NuclearUltrapower.main_no_embedding`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)*, OpenAI Math Release, September 23, 2026, result family 292, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.NuclearUltrapower.uniform_predecessors` of [lean/OAI/Analysis/NuclearUltrapower/Predecessors.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/Predecessors.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.NuclearUltrapower`, with `open Filter`, `open scoped Topology InnerProductSpace`):
--
--   ```lean
--   theorem uniform_predecessors (κ a : ℝ) (hgap : HasKazhdanGap.{u,u} S κ)
--       (hS : Subgroup.closure (S : Set Γ) = ⊤) (ha : a < κ) (ha0 : 0 < a)
--       (ht : ∀ g, f (θ g) * t = t * f g)
--       (hω : ∀ n : ℕ, ({n} : Set ℕ) ∉ (ω : Filter ℕ))
--       (h1 : ∀ n, u 1 n = 1)
--       (hmul : ∀ g h, Tendsto (fun n => ‖(u (g*h) n : B) - (u g n : B)*(u h n : B)‖)
--         (ω : Filter ℕ) (𝓝 0))
--       (π₀ : FiniteUnitaryRep.{u,u} Γ) (hirr₀ : π₀.Irreducible) :
--       ∀ᶠ n in (ω : Filter ℕ), ∀ π : FiniteUnitaryRep.{u,u} Γ,
--         π.Irreducible → Matches ρ S (fun g => u (f g) n) a π →
--         ∃ τ : FiniteUnitaryRep.{u,u} Γ, τ.Irreducible ∧
--           Matches ρ S (fun g => u (f g) n) a τ ∧ π.Embeds (τ.pull θ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.NuclearUltrapower.FiniteUnitaryRep`, `OAI.NuclearUltrapower.FiniteUnitaryRep.Embeds`, `OAI.NuclearUltrapower.FiniteUnitaryRep.Irreducible` and `OAI.NuclearUltrapower.FiniteUnitaryRep.pull` (definitions bundle `OAIQ019N001` of this split); `OAI.NuclearUltrapower.HasKazhdanGap` (definitions bundle `OAIQ019N002` of this split); `OAI.NuclearUltrapower.Matches` (definitions bundle `OAIQ019N043` of this split).
--
--   **Used by.** The proof of `OAI.NuclearUltrapower.contradiction_of_initial_match` of this split imports it.
-- source:
--   OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 292; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/NuclearUltrapower.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/Predecessors.lean (declaration OAI.NuclearUltrapower.uniform_predecessors)

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
universe u
section Predecessors
variable {Γ Δ B E : Type u} [Group Γ] [Group Δ] [CStarAlgebra B]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [Nontrivial E]
  (ρ : B →⋆ₐ[ℂ] (E →L[ℂ] E)) (f : Γ →* Δ)
  (θ : Monoid.End Γ) (hθ : Function.Injective θ) [Finite (Γ ⧸ θ.range)] (t : Δ)
  (S : Finset Γ) (u : Δ → ℕ → unitary B) (ω : Ultrafilter ℕ)

include hθ in
theorem uniform_predecessors (κ a : ℝ) (hgap : HasKazhdanGap.{u,u} S κ)
    (hS : Subgroup.closure (S : Set Γ) = ⊤) (ha : a < κ) (ha0 : 0 < a)
    (ht : ∀ g, f (θ g) * t = t * f g)
    (hω : ∀ n : ℕ, ({n} : Set ℕ) ∉ (ω : Filter ℕ))
    (h1 : ∀ n, u 1 n = 1)
    (hmul : ∀ g h, Tendsto (fun n => ‖(u (g*h) n : B) - (u g n : B)*(u h n : B)‖)
      (ω : Filter ℕ) (𝓝 0))
    (π₀ : FiniteUnitaryRep.{u,u} Γ) (hirr₀ : π₀.Irreducible) :
    ∀ᶠ n in (ω : Filter ℕ), ∀ π : FiniteUnitaryRep.{u,u} Γ,
      π.Irreducible → Matches ρ S (fun g => u (f g) n) a π →
      ∃ τ : FiniteUnitaryRep.{u,u} Γ, τ.Irreducible ∧
        Matches ρ S (fun g => u (f g) n) a τ ∧ π.Embeds (τ.pull θ) := by
  sorry

end Predecessors
end NuclearUltrapower
end
end

end OAI
end
