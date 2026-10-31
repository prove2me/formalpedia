-- Prove2me | Theorems.Thm_OAI_NuclearUltrapower_VariableUltra_quotient_tensor_no_invariants
-- name    : OAI.NuclearUltrapower.VariableUltra.quotient_tensor_no_invariants
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T07:55:55.314698+00:00
-- url     : https://prove2.me/theorems/ce9cf7f3-eabd-4a8c-a987-ca3010c308ff
-- title:
--   OAI.NuclearUltrapower.VariableUltra.quotient_tensor_no_invariants: intermediate lemma from OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.NuclearUltrapower.main_no_embedding`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)*, OpenAI Math Release, September 23, 2026, result family 292, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.NuclearUltrapower.VariableUltra.quotient_tensor_no_invariants` of [lean/OAI/Analysis/NuclearUltrapower/TensorGap.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/TensorGap.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.NuclearUltrapower.VariableUltra`, with `open scoped TensorProduct InnerProductSpace`, `open Module.End`, `open scoped CStarAlgebra`, `open Filter`, `open scoped Topology ENNReal`, `open scoped InnerProductSpace`, `open scoped TensorProduct`):
--
--   ```lean
--   theorem quotient_tensor_no_invariants {Γ : Type*} (S : Finset Γ)
--       (b : OrthonormalBasis n ℂ F) (U : ∀ i, Γ → (E i ≃ₗᵢ[ℂ] E i))
--       (V : Γ → (F ≃ₗᵢ[ℂ] F)) {κ : ℝ} (hκ0 : 0 < κ) (hκ : κ ≤ 4 * (S.card : ℝ))
--       (hgap : ∀ᶠ i in (ω : Filter ι), ∀ z : E i ⊗[ℂ] F,
--         κ * ‖z‖ ^ 2 ≤ ∑ s ∈ S, ‖TensorProduct.congrIsometry (U i s) (V s) z - z‖ ^ 2)
--       (φ : operatorQuotient E ω →⋆ₐ[ℂ] (K →L[ℂ] K))
--       (z : K ⊗[ℂ] F)
--       (hz : ∀ s ∈ S, TensorProduct.congrIsometry
--         (representedIso E ω φ (fun i => U i s)) (V s) z = z) : z = 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.NuclearUltrapower.VariableUltra.Seq`, `OAI.NuclearUltrapower.VariableUltra.con`, `OAI.NuclearUltrapower.VariableUltra.instStarAlgebra`, `OAI.NuclearUltrapower.VariableUltra.operatorQuotient` and `OAI.NuclearUltrapower.VariableUltra.representedIso` (definitions bundle `OAIQ019N001` of this split).
--
--   **Used by.** The proof of `OAI.NuclearUltrapower.VariableUltra.quotientRepresentation_weakly_mixing` of this split imports it.
-- source:
--   OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 292; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/NuclearUltrapower.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/TensorGap.lean (declaration OAI.NuclearUltrapower.VariableUltra.quotient_tensor_no_invariants)

import Mathlib
import Definitions.Def_OAIQ019N001

section

attribute [-instance] _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.instStarNormUltrapower _root_.OAI.NuclearUltrapower.lp_finiteDimensional
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
variable {ι : Type u} (E : ι → Type v)
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
  [∀ i, CompleteSpace (E i)] [∀ i, Nontrivial (E i)] (ω : Ultrafilter ι)

variable {K F : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

local instance operatorQuotientOrder_r2b64d4_1 : PartialOrder (operatorQuotient E ω) :=
  CStarAlgebra.spectralOrder _
local instance operatorQuotientStarOrder_r2b64d4_1 : StarOrderedRing (operatorQuotient E ω) :=
  CStarAlgebra.spectralOrderedRing _
theorem quotient_tensor_no_invariants {Γ : Type*} (S : Finset Γ)
    (b : OrthonormalBasis n ℂ F) (U : ∀ i, Γ → (E i ≃ₗᵢ[ℂ] E i))
    (V : Γ → (F ≃ₗᵢ[ℂ] F)) {κ : ℝ} (hκ0 : 0 < κ) (hκ : κ ≤ 4 * (S.card : ℝ))
    (hgap : ∀ᶠ i in (ω : Filter ι), ∀ z : E i ⊗[ℂ] F,
      κ * ‖z‖ ^ 2 ≤ ∑ s ∈ S, ‖TensorProduct.congrIsometry (U i s) (V s) z - z‖ ^ 2)
    (φ : operatorQuotient E ω →⋆ₐ[ℂ] (K →L[ℂ] K))
    (z : K ⊗[ℂ] F)
    (hz : ∀ s ∈ S, TensorProduct.congrIsometry
      (representedIso E ω φ (fun i => U i s)) (V s) z = z) : z = 0 := by
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
