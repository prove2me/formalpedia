-- Prove2me | Theorems.Thm_OAI_NuclearUltrapower_matchClasses_finite
-- name    : OAI.NuclearUltrapower.matchClasses_finite
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T07:09:23.893381+00:00
-- url     : https://prove2.me/theorems/1032895f-6d9d-45f3-803f-e1b258d7e344
-- title:
--   OAI.NuclearUltrapower.matchClasses_finite: intermediate lemma from OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.NuclearUltrapower.main_no_embedding`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)*, OpenAI Math Release, September 23, 2026, result family 292, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.NuclearUltrapower.matchClasses_finite` of [lean/OAI/Analysis/NuclearUltrapower/TensorMatching.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/TensorMatching.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.NuclearUltrapower`, with `open scoped InnerProductSpace ComplexOrder TensorProduct`):
--
--   ```lean
--   theorem matchClasses_finite (ω : Ultrafilter ℕ)
--       (hB : IsNuclear.{v,v} B) (κ a : ℝ)
--       (hS : S.Nonempty) (hκ0 : 0 < κ) (hκ : κ ≤ 4 * (S.card : ℝ))
--       (hgap : HasKazhdanGap.{u,v} S κ) (ha : a < κ ^ 2 / (4 * (S.card : ℝ)))
--       (hω : ∀ i : ℕ, ({i} : Set ℕ) ∉ (ω : Filter ℕ)) :
--       (matchClasses ρ S u a).Finite
--   ```
--
--   **Definitions.** The statement is written with `OAI.NuclearUltrapower.HasKazhdanGap` (definitions bundle `OAIQ019N002` of this split); `OAI.NuclearUltrapower.matchClasses` (definitions bundle `OAIQ019N043` of this split); `OAI.NuclearUltrapower.RepClass` (definitions bundle `OAIQ019N047` of this split); `OAI.NuclearUltrapower.IsNuclear` (the published bundle `Def_NuclearUltrapower`).
--
--   **Used by.** The proof of `OAI.NuclearUltrapower.contradiction_of_initial_match` of this split imports it.
-- source:
--   OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 292; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/NuclearUltrapower.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/TensorMatching.lean (declaration OAI.NuclearUltrapower.matchClasses_finite)

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
universe u v
open scoped InnerProductSpace ComplexOrder TensorProduct
namespace NuclearUltrapower
section Matching
variable {Γ : Type u} [Group Γ] {B E : Type v} [CStarAlgebra B]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [Nontrivial E]
  (ρ : B →⋆ₐ[ℂ] (E →L[ℂ] E)) (S : Finset Γ) (u : Γ → unitary B)

theorem matchClasses_finite (ω : Ultrafilter ℕ)
    (hB : IsNuclear.{v,v} B) (κ a : ℝ)
    (hS : S.Nonempty) (hκ0 : 0 < κ) (hκ : κ ≤ 4 * (S.card : ℝ))
    (hgap : HasKazhdanGap.{u,v} S κ) (ha : a < κ ^ 2 / (4 * (S.card : ℝ)))
    (hω : ∀ i : ℕ, ({i} : Set ℕ) ∉ (ω : Filter ℕ)) :
    (matchClasses ρ S u a).Finite := by
  sorry

end Matching
end NuclearUltrapower
end
end

end OAI
end
