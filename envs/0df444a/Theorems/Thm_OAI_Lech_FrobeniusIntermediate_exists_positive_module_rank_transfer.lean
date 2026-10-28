-- Prove2me | Theorems.Thm_OAI_Lech_FrobeniusIntermediate_exists_positive_module_rank_transfer
-- name    : OAI.Lech.FrobeniusIntermediate.exists_positive_module_rank_transfer
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T20:08:51.409488+00:00
-- url     : https://prove2.me/theorems/d85cc04e-7f57-425e-86c2-1c5e1c35729c
-- title:
--   OAI.Lech.FrobeniusIntermediate.exists_positive_module_rank_transfer: intermediate lemma from OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Lech.FrobeniusIntermediate`, with `open scoped TensorProduct ENNReal Topology`, `open Filter CategoryTheory`):
--
--   ```lean
--   theorem exists_positive_module_rank_transfer [IsNoetherianRing D] :
--       ∃ r : ℕ, 0 < r ∧ ∀ (e : ℕ) (he : ∀ x : D, x^(p^e) ∈ B)
--         (_hres : Function.Surjective (algebraMap (IsLocalRing.ResidueField B) (IsLocalRing.ResidueField D)))
--         (M : ModuleCat.{u} D), IsFiniteLength D M → ∀ a : ℝ≥0∞,
--         Tendsto (fun n => ((p : ℝ≥0∞)^(n*Lech.dimension B))⁻¹ *
--           (Module.length B (Lech.FrobeniusModule B p n
--             ((ModuleCat.extendScalars (powerMap p B e he)).obj M))).toENNReal)
--           atTop (𝓝 a) →
--         Tendsto (fun n => ((p : ℝ≥0∞)^(n*Lech.dimension B))⁻¹ *
--           (Module.length D (Lech.FrobeniusModule D p n M)).toENNReal)
--           atTop (𝓝 (((p : ℝ≥0∞)^(e*Lech.dimension B))⁻¹ * ((r : ℝ≥0∞)*a)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Lech.FrobeniusModule`, `OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions` and `OAI.Lech.FrobeniusIntermediate.powerMap` (definitions bundle `OAIQ032L004` of this split); `OAI.Lech.dimension` (the published bundle `Def_DuttaDomain`).
--
--   **Used by.** The proof of `OAI.Lech.SeparableOrder.exists_normalization_frobenius_module_limit` of this split imports it.
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
open Filter CategoryTheory
namespace Lech.FrobeniusIntermediate
universe u
variable {D : Type u} [CommRing D] [IsDomain D] [IsNoetherianRing D] [IsLocalRing D]
  (p : ℕ) [Fact p.Prime] [CharP D p]
  (B : Subring D) [IsLocalRing B] [IsNoetherianRing B] [IsLocalHom B.subtype]
  [Module.Finite B D]

omit [IsNoetherianRing D] in
theorem exists_positive_module_rank_transfer [IsNoetherianRing D] :
    ∃ r : ℕ, 0 < r ∧ ∀ (e : ℕ) (he : ∀ x : D, x^(p^e) ∈ B)
      (_hres : Function.Surjective (algebraMap (IsLocalRing.ResidueField B) (IsLocalRing.ResidueField D)))
      (M : ModuleCat.{u} D), IsFiniteLength D M → ∀ a : ℝ≥0∞,
      Tendsto (fun n => ((p : ℝ≥0∞)^(n*Lech.dimension B))⁻¹ *
        (Module.length B (Lech.FrobeniusModule B p n
          ((ModuleCat.extendScalars (powerMap p B e he)).obj M))).toENNReal)
        atTop (𝓝 a) →
      Tendsto (fun n => ((p : ℝ≥0∞)^(n*Lech.dimension B))⁻¹ *
        (Module.length D (Lech.FrobeniusModule D p n M)).toENNReal)
        atTop (𝓝 (((p : ℝ≥0∞)^(e*Lech.dimension B))⁻¹ * ((r : ℝ≥0∞)*a))) := by
  sorry
end Lech.FrobeniusIntermediate

end

end OAI
end
