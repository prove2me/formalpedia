-- Prove2me | Theorems.Thm_OAI_NuclearUltrapower_contradiction_of_initial_match
-- name    : OAI.NuclearUltrapower.contradiction_of_initial_match
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T07:06:20.987187+00:00
-- url     : https://prove2.me/theorems/82f56469-afad-4ee1-813e-474fcd783f6b
-- title:
--   OAI.NuclearUltrapower.contradiction_of_initial_match: intermediate lemma from OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.NuclearUltrapower.main_no_embedding`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)*, OpenAI Math Release, September 23, 2026, result family 292, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.NuclearUltrapower.contradiction_of_initial_match` of [lean/OAI/Analysis/NuclearUltrapower/Predecessors.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/Predecessors.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.NuclearUltrapower`, with `open Filter`, `open scoped Topology InnerProductSpace`):
--
--   ```lean
--   theorem contradiction_of_initial_match (κ a : ℝ)
--       (hB : IsNuclear.{u,u} B) (hSne : S.Nonempty)
--       (hκ0 : 0 < κ) (hκ : κ ≤ 4 * (S.card : ℝ))
--       (hgap : HasKazhdanGap.{u,u} S κ) (hS : Subgroup.closure (S : Set Γ) = ⊤)
--       (ha : a < κ) (ha0 : 0 < a) (ha' : a < κ^2 / (4 * (S.card : ℝ)))
--       (ht : ∀ g, f (θ g) * t = t * f g)
--       (hω : ∀ n : ℕ, ({n} : Set ℕ) ∉ (ω : Filter ℕ))
--       (h1 : ∀ n, u 1 n = 1)
--       (hmul : ∀ g h, Tendsto (fun n => ‖(u (g*h) n : B) - (u g n : B)*(u h n : B)‖)
--         (ω : Filter ℕ) (𝓝 0))
--       (π : FiniteUnitaryRep.{u,u} Γ) (hirr : π.Irreducible)
--       (haper : ∀ p : ℕ, 0 < p → ¬ π.Equivalent (π.pull (θ^p)))
--       (hm : ∀ᶠ n in (ω : Filter ℕ), Matches ρ S (fun g => u (f g) n) a π) : False
--   ```
--
--   **Definitions.** The statement is written with `OAI.NuclearUltrapower.FiniteUnitaryRep`, `OAI.NuclearUltrapower.FiniteUnitaryRep.Equivalent`, `OAI.NuclearUltrapower.FiniteUnitaryRep.Irreducible` and `OAI.NuclearUltrapower.FiniteUnitaryRep.pull` (definitions bundle `OAIQ019N001` of this split); `OAI.NuclearUltrapower.HasKazhdanGap` (definitions bundle `OAIQ019N002` of this split); `OAI.NuclearUltrapower.Matches` (definitions bundle `OAIQ019N043` of this split); `OAI.NuclearUltrapower.IsNuclear` (the published bundle `Def_NuclearUltrapower`).
--
--   **Used by.** The proof of `OAI.NuclearUltrapower.fullGroup_no_nuclear_ultrapower` of this split imports it.
-- source:
--   OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 292; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/NuclearUltrapower.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/Predecessors.lean (declaration OAI.NuclearUltrapower.contradiction_of_initial_match)

import Mathlib
import Definitions.Def_NuclearUltrapower
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
theorem contradiction_of_initial_match (κ a : ℝ)
    (hB : IsNuclear.{u,u} B) (hSne : S.Nonempty)
    (hκ0 : 0 < κ) (hκ : κ ≤ 4 * (S.card : ℝ))
    (hgap : HasKazhdanGap.{u,u} S κ) (hS : Subgroup.closure (S : Set Γ) = ⊤)
    (ha : a < κ) (ha0 : 0 < a) (ha' : a < κ^2 / (4 * (S.card : ℝ)))
    (ht : ∀ g, f (θ g) * t = t * f g)
    (hω : ∀ n : ℕ, ({n} : Set ℕ) ∉ (ω : Filter ℕ))
    (h1 : ∀ n, u 1 n = 1)
    (hmul : ∀ g h, Tendsto (fun n => ‖(u (g*h) n : B) - (u g n : B)*(u h n : B)‖)
      (ω : Filter ℕ) (𝓝 0))
    (π : FiniteUnitaryRep.{u,u} Γ) (hirr : π.Irreducible)
    (haper : ∀ p : ℕ, 0 < p → ¬ π.Equivalent (π.pull (θ^p)))
    (hm : ∀ᶠ n in (ω : Filter ℕ), Matches ρ S (fun g => u (f g) n) a π) : False := by
  sorry

end Predecessors
end NuclearUltrapower
end
end

end OAI
end
