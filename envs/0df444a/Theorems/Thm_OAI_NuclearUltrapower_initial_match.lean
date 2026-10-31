-- Prove2me | Theorems.Thm_OAI_NuclearUltrapower_initial_match
-- name    : OAI.NuclearUltrapower.initial_match
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T07:08:18.289064+00:00
-- url     : https://prove2.me/theorems/4fc0db7d-7b3e-4d6b-947d-5b57da3f0de1
-- title:
--   OAI.NuclearUltrapower.initial_match: intermediate lemma from OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.NuclearUltrapower.main_no_embedding`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)*, OpenAI Math Release, September 23, 2026, result family 292, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.NuclearUltrapower.initial_match` of [lean/OAI/Analysis/NuclearUltrapower/InitialMatching.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/InitialMatching.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.NuclearUltrapower`, with `open Filter`, `open scoped Topology InnerProductSpace TensorProduct`):
--
--   ```lean
--   theorem initial_match (π : FiniteUnitaryRep.{u,u} Γ) (a : ℝ)
--       (ha0 : 0 < a) (ha : a ≤ 4 * (S.card : ℝ))
--       (z : K ⊗[ℂ] π) (hz0 : z ≠ 0)
--       (hz : ∀ s ∈ S, TensorProduct.congrIsometry (σ s) (π.action s) z = z) :
--       ∀ᶠ n in (ω : Filter ℕ), Matches ρ S (fun g => u g n) a π
--   ```
--
--   **Definitions.** The statement is written with `OAI.NuclearUltrapower.FiniteUnitaryRep`, `OAI.NuclearUltrapower.VariableUltra.Algebra`, `OAI.NuclearUltrapower.VariableUltra.Seq`, `OAI.NuclearUltrapower.VariableUltra.con`, `OAI.NuclearUltrapower.VariableUltra.instStarAlgebra`, `OAI.NuclearUltrapower.VariableUltra.mk` and `OAI.NuclearUltrapower.VariableUltra.unitarySequence` (definitions bundle `OAIQ019N001` of this split); `OAI.NuclearUltrapower.Matches` (definitions bundle `OAIQ019N043` of this split).
--
--   **Used by.** The proof of `OAI.NuclearUltrapower.fullGroup_no_nuclear_ultrapower` of this split imports it.
-- source:
--   OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 292; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/NuclearUltrapower.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/InitialMatching.lean (declaration OAI.NuclearUltrapower.initial_match)

import Mathlib
import Definitions.Def_OAIQ019N043

section

attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzPolynomial.instInvolutiveStarWord _root_.OAI.NuclearUltrapower.CuntzPolynomial.instStarWord _root_.OAI.NuclearUltrapower.CuntzWords.instDecidableEqWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Filter
open scoped Topology InnerProductSpace TensorProduct
namespace NuclearUltrapower
universe u
section InitialMatch
variable {Γ A B E K : Type u} [Group Γ] [CStarAlgebra A] [CStarAlgebra B] [Nontrivial B]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (ρ : B →⋆ₐ[ℂ] (E →L[ℂ] E)) (hρ : Function.Injective ρ)
  (S : Finset Γ) (ω : Ultrafilter ℕ)
  (φ : A →⋆ₐ[ℂ] VariableUltra.Algebra (fun _ : ℕ => B) ω) (hφ : Function.Injective φ)
  (w : Γ → A) (u : Γ → ℕ → unitary B)
  (hu : ∀ g, φ (w g) = VariableUltra.mk (fun _ : ℕ => B) ω
    (VariableUltra.unitarySequence (fun _ : ℕ => B) (u g)))
  (ψ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (σ : Γ → K ≃ₗᵢ[ℂ] K)
  (hψ : ∀ g, ψ (w g) = (σ g : K →L[ℂ] K))

attribute [local instance] OAI.NuclearUltrapower.instPartialOrderAlgebraNat
local instance instPartialOrder_solutions_2_r4306c6_1 : PartialOrder A := CStarAlgebra.spectralOrder A
attribute [local instance] OAI.NuclearUltrapower.instPartialOrder_solutions_3
local instance instStarOrderedRingAlgebraNat_r4306c6_1 : StarOrderedRing (VariableUltra.Algebra (fun _ : ℕ => B) ω) :=
  CStarAlgebra.spectralOrderedRing _
include hρ hu hφ hψ in
theorem initial_match (π : FiniteUnitaryRep.{u,u} Γ) (a : ℝ)
    (ha0 : 0 < a) (ha : a ≤ 4 * (S.card : ℝ))
    (z : K ⊗[ℂ] π) (hz0 : z ≠ 0)
    (hz : ∀ s ∈ S, TensorProduct.congrIsometry (σ s) (π.action s) z = z) :
    ∀ᶠ n in (ω : Filter ℕ), Matches ρ S (fun g => u g n) a π := by
  sorry
end InitialMatch
end NuclearUltrapower
end
end

end OAI
end
