-- Prove2me | Theorems.Thm_OAI_NuclearUltrapower_VariableUltra_quotientRepresentation_weakly_mixing
-- name    : OAI.NuclearUltrapower.VariableUltra.quotientRepresentation_weakly_mixing
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T06:59:33.761493+00:00
-- url     : https://prove2.me/theorems/b315b794-1774-4663-ace9-db400cd7b039
-- title:
--   OAI.NuclearUltrapower.VariableUltra.quotientRepresentation_weakly_mixing: intermediate lemma from OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.NuclearUltrapower.main_no_embedding`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)*, OpenAI Math Release, September 23, 2026, result family 292, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.NuclearUltrapower.VariableUltra.quotientRepresentation_weakly_mixing` of [lean/OAI/Analysis/NuclearUltrapower/RepresentationUltraproduct.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/RepresentationUltraproduct.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.NuclearUltrapower.VariableUltra`, with `open scoped TensorProduct InnerProductSpace`, `open Module.End`, `open scoped CStarAlgebra`, `open Filter`, `open scoped Topology ENNReal`, `open scoped InnerProductSpace`, `open scoped TensorProduct`):
--
--   ```lean
--   theorem quotientRepresentation_weakly_mixing
--       (hω : ∀ i : ι, ({i} : Set ι) ∉ (ω : Filter ι))
--       (hirr : ∀ i, (π i).Irreducible)
--       (hne : Pairwise (fun i j => ¬ (π i).Equivalent (π j)))
--       (S : Finset Γ) (κ : ℝ) (hκ0 : 0 < κ) (hκ : κ ≤ 4 * (S.card : ℝ))
--       (hgap : HasKazhdanGap.{u,v} S κ)
--       (φ : operatorQuotient (fun i => π i) ω →⋆ₐ[ℂ] (K →L[ℂ] K)) :
--       HasNoFiniteDimensionalSubrep (quotientRepresentation π ω φ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.NuclearUltrapower.FiniteUnitaryRep`, `OAI.NuclearUltrapower.FiniteUnitaryRep.Equivalent`, `OAI.NuclearUltrapower.FiniteUnitaryRep.Irreducible`, `OAI.NuclearUltrapower.VariableUltra.Seq`, `OAI.NuclearUltrapower.VariableUltra.con`, `OAI.NuclearUltrapower.VariableUltra.instStarAlgebra` and `OAI.NuclearUltrapower.VariableUltra.operatorQuotient` (definitions bundle `OAIQ019N001` of this split); `OAI.NuclearUltrapower.HasKazhdanGap` and `OAI.NuclearUltrapower.HasNoFiniteDimensionalSubrep` (definitions bundle `OAIQ019N002` of this split); `OAI.NuclearUltrapower.VariableUltra.quotientRepresentation` (definitions bundle `OAIQ019N040` of this split).
--
--   **Used by.** The proof of `OAI.NuclearUltrapower.matchClasses_finite` of this split imports it.
-- source:
--   OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 292; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/NuclearUltrapower.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/RepresentationUltraproduct.lean (declaration OAI.NuclearUltrapower.VariableUltra.quotientRepresentation_weakly_mixing)

import Mathlib
import Definitions.Def_OAIQ019N040

section

attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzPolynomial.instStarWord _root_.OAI.NuclearUltrapower.CuntzWords.instDecidableEqWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.instStarNormUltrapower _root_.OAI.NuclearUltrapower.lp_finiteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
noncomputable section
open scoped TensorProduct InnerProductSpace
open Module.End
noncomputable section
open scoped CStarAlgebra
noncomputable section
open Filter
open scoped Topology ENNReal
noncomputable section
open scoped InnerProductSpace
namespace NuclearUltrapower
open scoped TensorProduct

namespace VariableUltra
variable {ι : Type*} {Γ : Type u} [Group Γ]
variable (π : ι → FiniteUnitaryRep.{u,v} Γ)

variable (ω : Ultrafilter ι) {K : Type v}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem quotientRepresentation_weakly_mixing
    (hω : ∀ i : ι, ({i} : Set ι) ∉ (ω : Filter ι))
    (hirr : ∀ i, (π i).Irreducible)
    (hne : Pairwise (fun i j => ¬ (π i).Equivalent (π j)))
    (S : Finset Γ) (κ : ℝ) (hκ0 : 0 < κ) (hκ : κ ≤ 4 * (S.card : ℝ))
    (hgap : HasKazhdanGap.{u,v} S κ)
    (φ : operatorQuotient (fun i => π i) ω →⋆ₐ[ℂ] (K →L[ℂ] K)) :
    HasNoFiniteDimensionalSubrep (quotientRepresentation π ω φ) := by
  sorry
end VariableUltra
end NuclearUltrapower

end
end
end
end
end

end OAI
end
