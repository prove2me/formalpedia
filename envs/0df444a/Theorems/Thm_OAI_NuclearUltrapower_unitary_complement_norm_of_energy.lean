-- Prove2me | Theorems.Thm_OAI_NuclearUltrapower_unitary_complement_norm_of_energy
-- name    : OAI.NuclearUltrapower.unitary_complement_norm_of_energy
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T07:55:52.934192+00:00
-- url     : https://prove2.me/theorems/66bc9bb5-6d9e-4e37-aedf-af4a20ad84a2
-- title:
--   OAI.NuclearUltrapower.unitary_complement_norm_of_energy: intermediate lemma from OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.NuclearUltrapower.main_no_embedding`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)*, OpenAI Math Release, September 23, 2026, result family 292, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.NuclearUltrapower.unitary_complement_norm_of_energy` of [lean/OAI/Analysis/NuclearUltrapower/SpatialGap.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/SpatialGap.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.NuclearUltrapower`, with `open scoped TensorProduct InnerProductSpace`, `open Module.End`, `open scoped CStarAlgebra`, `open Filter`, `open scoped Topology ENNReal`, `open scoped InnerProductSpace`, `open scoped TensorProduct InnerProductSpace`, `open scoped TensorProduct`, `open scoped InnerProductSpace TensorProduct`, `open scoped TensorProduct InnerProductSpace ComplexOrder`):
--
--   ```lean
--   theorem unitary_complement_norm_of_energy {J T : Type*} [NormedAddCommGroup T]
--       [InnerProductSpace ℂ T] [CompleteSpace T] (S : Finset J)
--       (U : J → unitary (T →L[ℂ] T)) (b : ℝ) (hb : b ≤ 4 * (S.card : ℝ))
--       (he : ∀ x : T, b * ‖x‖ ^ 2 ≤ ∑ s ∈ S, ‖(U s : T →L[ℂ] T) x - x‖ ^ 2) :
--       ‖(4 * (S.card : ℂ)) • (1 : T →L[ℂ] T) -
--           laplacian S (fun s => (U s : T →L[ℂ] T))‖ ≤ 4 * (S.card : ℝ) - b
--   ```
--
--   **Definitions.** The statement is written with `OAI.NuclearUltrapower.laplacian` (definitions bundle `OAIQ019N028` of this split).
--
--   **Used by.** The proof of `OAI.NuclearUltrapower.matchClasses_finite` of this split imports it.
-- source:
--   OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 292; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/NuclearUltrapower.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/SpatialGap.lean (declaration OAI.NuclearUltrapower.unitary_complement_norm_of_energy)

import Mathlib
import Definitions.Def_OAIQ019N028

section

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
noncomputable section
open scoped TensorProduct InnerProductSpace
noncomputable section
open scoped TensorProduct
noncomputable section
open scoped InnerProductSpace TensorProduct
namespace NuclearUltrapower
open scoped TensorProduct InnerProductSpace ComplexOrder

section SpatialGap
variable {Γ : Type u} [Group Γ] {B C : Type v} [CStarAlgebra B] [CStarAlgebra C]

theorem unitary_complement_norm_of_energy {J T : Type*} [NormedAddCommGroup T]
    [InnerProductSpace ℂ T] [CompleteSpace T] (S : Finset J)
    (U : J → unitary (T →L[ℂ] T)) (b : ℝ) (hb : b ≤ 4 * (S.card : ℝ))
    (he : ∀ x : T, b * ‖x‖ ^ 2 ≤ ∑ s ∈ S, ‖(U s : T →L[ℂ] T) x - x‖ ^ 2) :
    ‖(4 * (S.card : ℂ)) • (1 : T →L[ℂ] T) -
        laplacian S (fun s => (U s : T →L[ℂ] T))‖ ≤ 4 * (S.card : ℝ) - b := by
  sorry

end SpatialGap
end NuclearUltrapower

end
end
end
end
end
end
end
end

end OAI
end
