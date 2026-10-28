-- Prove2me | Theorems.Thm_OAI_Lech_exists_frobenius_tensor_transfer
-- name    : OAI.Lech.exists_frobenius_tensor_transfer
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T20:17:23.292863+00:00
-- url     : https://prove2.me/theorems/9174a343-1079-4973-aebc-85367f67d5f3
-- title:
--   OAI.Lech.exists_frobenius_tensor_transfer: intermediate lemma from OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Lech`, with `open scoped TensorProduct ENNReal Topology`, `open Filter`):
--
--   ```lean
--   theorem exists_frobenius_tensor_transfer
--       (hfaithful : ∀ g : B, g ≠ 0 → g • (LinearMap.id : E →ₗ[B] E) ≠ 0) :
--       ∃ r : ℕ, 0 < r ∧ ∀ (M : ModuleCat.{u} B), IsFiniteLength B M → ∀ a : ℝ≥0∞,
--         Tendsto (fun n => ((p : ℝ≥0∞)^(n*Lech.dimension B))⁻¹ *
--           (Module.length B (FrobeniusModule B p n M)).toENNReal) atTop (𝓝 a) →
--         Tendsto (fun n => ((p : ℝ≥0∞)^(n*Lech.dimension B))⁻¹ *
--           (Module.length B (E ⊗[B] (FrobeniusModule B p n M))).toENNReal)
--           atTop (𝓝 ((r : ℝ≥0∞)*a))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Lech.FrobeniusModule` (definitions bundle `OAIQ032L004` of this split); `OAI.Lech.dimension` (the published bundle `Def_DuttaDomain`).
--
--   **Used by.** The proof of `OAI.Lech.FrobeniusIntermediate.exists_positive_module_rank_transfer` of this split imports it.
-- source:
--   OpenAI, Lech's multiplicity conjecture (result family 194), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 194; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_DuttaDomain
import Definitions.Def_OAIQ032L004

section

attribute [-instance] _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal Topology
open Filter
namespace Lech
universe u
variable (B E : Type u) [CommRing B] [IsDomain B] [IsLocalRing B] [IsNoetherianRing B]
  [CommRing E] [Algebra B E] [Module.Finite B E]
  (p : ℕ) [Fact p.Prime] [CharP B p]

theorem exists_frobenius_tensor_transfer
    (hfaithful : ∀ g : B, g ≠ 0 → g • (LinearMap.id : E →ₗ[B] E) ≠ 0) :
    ∃ r : ℕ, 0 < r ∧ ∀ (M : ModuleCat.{u} B), IsFiniteLength B M → ∀ a : ℝ≥0∞,
      Tendsto (fun n => ((p : ℝ≥0∞)^(n*Lech.dimension B))⁻¹ *
        (Module.length B (FrobeniusModule B p n M)).toENNReal) atTop (𝓝 a) →
      Tendsto (fun n => ((p : ℝ≥0∞)^(n*Lech.dimension B))⁻¹ *
        (Module.length B (E ⊗[B] (FrobeniusModule B p n M))).toENNReal)
        atTop (𝓝 ((r : ℝ≥0∞)*a)) := by
  sorry
end Lech

end

end OAI
end
