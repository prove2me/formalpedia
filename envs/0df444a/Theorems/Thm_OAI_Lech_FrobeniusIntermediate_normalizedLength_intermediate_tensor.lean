-- Prove2me | Theorems.Thm_OAI_Lech_FrobeniusIntermediate_normalizedLength_intermediate_tensor
-- name    : OAI.Lech.FrobeniusIntermediate.normalizedLength_intermediate_tensor
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T20:34:27.271621+00:00
-- url     : https://prove2.me/theorems/c14f9bf8-07ae-498f-9a51-cac8e63b8f3d
-- title:
--   OAI.Lech.FrobeniusIntermediate.normalizedLength_intermediate_tensor: intermediate lemma from OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Lech.FrobeniusIntermediate`, with `open scoped TensorProduct ENNReal`, `open CategoryTheory`, `open Lech.RootTower Lech.PerfectDomainStages`):
--
--   ```lean
--   theorem normalizedLength_intermediate_tensor (M : ModuleCat.{u} D) :
--       normalizedLength σ k p ((PerfectClosure D p) ⊗[D] M) =
--         ((p : ℝ≥0∞)^(e*Fintype.card σ))⁻¹ *
--           normalizedLength σ k p ((PerfectClosure B p) ⊗[B]
--             ((ModuleCat.extendScalars (powerMap p B.toSubring e he)).obj M))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubalgebraMvPowerSeries_solutions_1`, `OAI.Lech.FrobeniusIntermediate.instSMulCommClassSubtypeMemSubalgebraMvPowerSeriesPerfectClosure_solutions`, `OAI.Lech.FrobeniusIntermediate.powerMap`, `OAI.Lech.PerfectDomainStages.domainAlgebra`, `OAI.Lech.RootTower.perfectAlgebra` and `OAI.Lech.RootTower.powerSeriesCharP` (definitions bundle `OAIQ032L004` of this split); `OAI.Lech.RootTower.normalizedLength` (definitions bundle `OAIQ032L023` of this split).
--
--   **Used by.** The proof of `OAI.Lech.SeparableOrder.exists_normalization_frobenius_module_limit` of this split imports it.
-- source:
--   OpenAI, Lech's multiplicity conjecture (result family 194), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 194; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ032L023

section

attribute [-instance] _root_.OAI.Lech.PerfectDomainStages.rootStageFunctor_preservesFiniteColimits _root_.OAI.Lech.PerfectDomainStages.rootStageFunctor_preservesZero _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal
open CategoryTheory
namespace Lech.FrobeniusIntermediate
open Lech.RootTower Lech.PerfectDomainStages
universe u
variable (σ : Type) (k D : Type u) [Fintype σ] [Field k] [CommRing D] [IsDomain D]
    [Algebra (MvPowerSeries σ k) D]
    (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p] [CharP D p]
    (B : Subalgebra (MvPowerSeries σ k) D)
    (e : ℕ) (he : ∀ x : D, x^(p^e) ∈ B)

attribute [local instance] OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubalgebraMvPowerSeries_solutions_1
attribute [local instance] OAI.Lech.FrobeniusIntermediate.instSMulCommClassSubtypeMemSubalgebraMvPowerSeriesPerfectClosure_solutions
theorem normalizedLength_intermediate_tensor (M : ModuleCat.{u} D) :
    normalizedLength σ k p ((PerfectClosure D p) ⊗[D] M) =
      ((p : ℝ≥0∞)^(e*Fintype.card σ))⁻¹ *
        normalizedLength σ k p ((PerfectClosure B p) ⊗[B]
          ((ModuleCat.extendScalars (powerMap p B.toSubring e he)).obj M)) := by
  sorry
end Lech.FrobeniusIntermediate

end

end OAI
end
