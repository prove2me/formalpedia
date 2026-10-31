-- Prove2me | Theorems.Thm_OAI_NuclearUltrapower_fullGroup_no_nuclear_ultrapower
-- name    : OAI.NuclearUltrapower.fullGroup_no_nuclear_ultrapower
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T07:08:25.811223+00:00
-- url     : https://prove2.me/theorems/9269c48c-fabb-41bc-811a-a2c14e630009
-- title:
--   OAI.NuclearUltrapower.fullGroup_no_nuclear_ultrapower: intermediate lemma from OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.NuclearUltrapower.main_no_embedding`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)*, OpenAI Math Release, September 23, 2026, result family 292, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.NuclearUltrapower.fullGroup_no_nuclear_ultrapower` of [lean/OAI/Analysis/NuclearUltrapower/GroupObstruction.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/GroupObstruction.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.NuclearUltrapower`, with `open Filter`, `open scoped Topology InnerProductSpace TensorProduct`):
--
--   ```lean
--   theorem fullGroup_no_nuclear_ultrapower (hB : IsNuclear.{0,0} B)
--       (ω : Ultrafilter ℕ) (hω : IsFree ω) :
--       ¬ ∃ φ : FullGroupModel.Full Δ →⋆ₐ[ℂ] NormUltrapower B ω,
--         Function.Injective φ
--   ```
--
--   **Definitions.** The statement is written with `OAI.NuclearUltrapower.FiniteUnitaryRep`, `OAI.NuclearUltrapower.FiniteUnitaryRep.Equivalent`, `OAI.NuclearUltrapower.FiniteUnitaryRep.Irreducible` and `OAI.NuclearUltrapower.FiniteUnitaryRep.pull` (definitions bundle `OAIQ019N001` of this split); `OAI.NuclearUltrapower.HasKazhdanGap` (definitions bundle `OAIQ019N002` of this split); `OAI.NuclearUltrapower.FullGroupModel.instCStarAlgebraFull` (definitions bundle `OAIQ019N043` of this split); `OAI.NuclearUltrapower.FullGroupModel.Full` (definitions bundle `OAIQ019N047` of this split); `OAI.NuclearUltrapower.BoundedSeq`, `OAI.NuclearUltrapower.IsFree`, `OAI.NuclearUltrapower.IsNuclear`, `OAI.NuclearUltrapower.NormUltrapower`, `OAI.NuclearUltrapower.instStarNormUltrapower` and `OAI.NuclearUltrapower.ultraCon` (the published bundle `Def_NuclearUltrapower`).
--
--   **Used by.** The proof of `OAI.NuclearUltrapower.main_statement` of this split imports it.
-- source:
--   OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 292; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/NuclearUltrapower.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/GroupObstruction.lean (declaration OAI.NuclearUltrapower.fullGroup_no_nuclear_ultrapower)

import Mathlib
import Definitions.Def_NuclearUltrapower
import Definitions.Def_OAIQ019N043

section

attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzPolynomial.instInvolutiveStarWord _root_.OAI.NuclearUltrapower.CuntzPolynomial.instStarWord
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

section Obstruction
variable {Γ Δ B : Type} [Group Γ] [Group Δ] [CStarAlgebra B] [Nontrivial B]
  (f : Γ →* Δ) (hf : Function.Injective f)
  (θ : Monoid.End Γ) (hθ : Function.Injective θ) [Finite (Γ ⧸ θ.range)]
  (t : Δ) (ht : ∀ g, f (θ g) * t = t * f g)
  (S : Finset Γ) (hSne : S.Nonempty) (hS : Subgroup.closure (S : Set Γ) = ⊤)
  (κ : ℝ) (hκ0 : 0 < κ) (hκ : κ ≤ 4 * (S.card : ℝ))
  (hgap : HasKazhdanGap.{0,0} S κ)
  (π : FiniteUnitaryRep.{0,0} Γ) (hirr : π.Irreducible)
  (haper : ∀ p : ℕ, 0 < p → ¬ π.Equivalent (π.pull (θ^p)))

include hf hθ ht hSne hS hκ0 hκ hgap hirr haper in
theorem fullGroup_no_nuclear_ultrapower (hB : IsNuclear.{0,0} B)
    (ω : Ultrafilter ℕ) (hω : IsFree ω) :
    ¬ ∃ φ : FullGroupModel.Full Δ →⋆ₐ[ℂ] NormUltrapower B ω,
      Function.Injective φ := by
  sorry
end Obstruction
end NuclearUltrapower
end
end

end OAI
end
