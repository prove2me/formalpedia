-- Prove2me | Theorems.Thm_OAI_NuclearUltrapower_nuclear_coordinate_bound
-- name    : OAI.NuclearUltrapower.nuclear_coordinate_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T09:44:12.254019+00:00
-- url     : https://prove2.me/theorems/b83e4ad5-5c2a-4196-ae1a-f709827bd96b
-- title:
--   OAI.NuclearUltrapower.nuclear_coordinate_bound: intermediate lemma from OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.NuclearUltrapower.main_no_embedding`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)*, OpenAI Math Release, September 23, 2026, result family 292, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.NuclearUltrapower.nuclear_coordinate_bound` of [lean/OAI/Analysis/NuclearUltrapower/NuclearFiniteness.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/NuclearFiniteness.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.NuclearUltrapower`, with `open Filter`, `open scoped InnerProductSpace TensorProduct Topology ENNReal ComplexOrder`):
--
--   ```lean
--   theorem nuclear_coordinate_bound
--       (hB : IsNuclear.{v,v} B) (S : Finset Γ) (κ : ℝ)
--       (hS : S.Nonempty) (hκ0 : 0 < κ) (hκ : κ ≤ 4 * (S.card : ℝ))
--       (hgap : HasKazhdanGap.{u,v} S κ)
--       (hω : ∀ i : ℕ, ({i} : Set ℕ) ∉ (ω : Filter ℕ))
--       (hirr : ∀ i, (π i).Irreducible)
--       (hne : Pairwise (fun i j => ¬ (π i).Equivalent (π j)))
--       (u : Γ → unitary B) :
--       ‖finiteTensorAction (E := E) π ω (coordinateComplement ρ π S u)‖ ≤
--         4 * (S.card : ℝ) - κ ^ 2 / (4 * (S.card : ℝ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.NuclearUltrapower.TensorHilbert` (definitions bundle `OAIQ019N000` of this split); `OAI.NuclearUltrapower.FiniteUnitaryRep`, `OAI.NuclearUltrapower.FiniteUnitaryRep.Equivalent`, `OAI.NuclearUltrapower.FiniteUnitaryRep.Irreducible` and `OAI.NuclearUltrapower.VariableUltra.Seq` (definitions bundle `OAIQ019N001` of this split); `OAI.NuclearUltrapower.HasKazhdanGap` (definitions bundle `OAIQ019N002` of this split); `OAI.NuclearUltrapower.coordinateComplement` (definitions bundle `OAIQ019N043` of this split); `OAI.NuclearUltrapower.finiteTensorAction`, `OAI.NuclearUltrapower.finiteTensorHilbert` and `OAI.NuclearUltrapower.tensorHilbertNontrivial` (definitions bundle `OAIQ019N046` of this split); `OAI.NuclearUltrapower.IsNuclear` and `OAI.NuclearUltrapower.ComplexHilbert` (the published bundle `Def_NuclearUltrapower`).
--
--   **Used by.** The proof of `OAI.NuclearUltrapower.matchClasses_finite` of this split imports it.
-- source:
--   OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 292; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/NuclearUltrapower.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/NuclearFiniteness.lean (declaration OAI.NuclearUltrapower.nuclear_coordinate_bound)

import Mathlib
import Definitions.Def_NuclearUltrapower
import Definitions.Def_OAIQ019N043

section

attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzPolynomial.instInvolutiveStarWord _root_.OAI.NuclearUltrapower.CuntzPolynomial.instStarWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
universe u v
open Filter
open scoped InnerProductSpace TensorProduct Topology ENNReal ComplexOrder
namespace NuclearUltrapower
section NuclearFiniteness
variable {Γ : Type u} [Group Γ] {B : Type v} [CStarAlgebra B]
  {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [Nontrivial E]
  (ρ : B →⋆ₐ[ℂ] (E →L[ℂ] E)) (π : ℕ → FiniteUnitaryRep.{u,v} Γ) (ω : Ultrafilter ℕ)

theorem nuclear_coordinate_bound
    (hB : IsNuclear.{v,v} B) (S : Finset Γ) (κ : ℝ)
    (hS : S.Nonempty) (hκ0 : 0 < κ) (hκ : κ ≤ 4 * (S.card : ℝ))
    (hgap : HasKazhdanGap.{u,v} S κ)
    (hω : ∀ i : ℕ, ({i} : Set ℕ) ∉ (ω : Filter ℕ))
    (hirr : ∀ i, (π i).Irreducible)
    (hne : Pairwise (fun i j => ¬ (π i).Equivalent (π j)))
    (u : Γ → unitary B) :
    ‖finiteTensorAction (E := E) π ω (coordinateComplement ρ π S u)‖ ≤
      4 * (S.card : ℝ) - κ ^ 2 / (4 * (S.card : ℝ)) := by
  sorry

end NuclearFiniteness
end NuclearUltrapower
end
end

end OAI
end
