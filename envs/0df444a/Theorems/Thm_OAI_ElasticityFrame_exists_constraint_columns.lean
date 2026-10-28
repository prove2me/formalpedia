-- Prove2me | Theorems.Thm_OAI_ElasticityFrame_exists_constraint_columns
-- name    : OAI.ElasticityFrame.exists_constraint_columns
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T10:28:59.240086+00:00
-- url     : https://prove2.me/theorems/12ebbbd5-a5a2-43ee-a61a-b002d4538fe5
-- title:
--   OAI.ElasticityFrame.exists_constraint_columns: intermediate lemma from OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Elasticity.global_uniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem*, OpenAI Math Release, September 24, 2026, result family 372, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElasticityFrame.exists_constraint_columns` of [lean/OAI/MathematicalPhysics/Elasticity/Transport.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/Transport.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElasticityFrame`, with `open Set Complex Module`, `open scoped BigOperators`):
--
--   ```lean
--   theorem exists_constraint_columns (θ : Fin 3 → ℂ) (hθ : ∑ i,θ i*θ i=0) (hne : θ≠0)
--       (t : X → ℂ) (q : Fin 3 → X → ℂ)
--       (ht : ContDiff ℝ (⊤ : ℕ∞) t) (hq : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (q i))
--       {C : Set X} (hC : IsCompact C) :
--       ∃ B : X → Basis (Fin 3) ℂ (Fiber θ),
--         (∀ ν, ContDiff ℝ (⊤ : ℕ∞) (fun x => B x ν)) ∧
--         ∀ ν x, x∈C →
--           fderiv ℝ (fun x => B x ν) x (ElasticityParameter.characteristicPlane ElasticityParameter.basis θ 1)+
--             I • fderiv ℝ (fun x => B x ν) x (ElasticityParameter.characteristicPlane ElasticityParameter.basis θ I)=
--             connection θ hθ (t x) (fun i => q i x) (B x ν)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElasticityFrame.Amp`, `OAI.ElasticityFrame.Fiber`, `OAI.ElasticityFrame.X`, `OAI.ElasticityFrame.connection`, `OAI.ElasticityFrame.fiber`, `OAI.ElasticityParameter.X` and `OAI.ElasticityParameter.basis` (definitions bundle `OAIQ6El002` of this split); `OAI.ElasticityParameter.characteristicPlane` (definitions bundle `OAIQ6El003` of this split).
--
--   **Used by.** The proof of `OAI.ElasticityAugmented.exists_physical_leading_frame` of this split imports it.
-- source:
--   OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 372; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/Transport.lean (declaration OAI.ElasticityFrame.exists_constraint_columns)

import Mathlib
import Definitions.Def_OAIQ6El002
import Definitions.Def_OAIQ6El003

section

attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open Set Complex Module
open scoped BigOperators
namespace ElasticityFrame

theorem exists_constraint_columns (θ : Fin 3 → ℂ) (hθ : ∑ i,θ i*θ i=0) (hne : θ≠0)
    (t : X → ℂ) (q : Fin 3 → X → ℂ)
    (ht : ContDiff ℝ (⊤ : ℕ∞) t) (hq : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (q i))
    {C : Set X} (hC : IsCompact C) :
    ∃ B : X → Basis (Fin 3) ℂ (Fiber θ),
      (∀ ν, ContDiff ℝ (⊤ : ℕ∞) (fun x => B x ν)) ∧
      ∀ ν x, x∈C →
        fderiv ℝ (fun x => B x ν) x (ElasticityParameter.characteristicPlane ElasticityParameter.basis θ 1)+
          I • fderiv ℝ (fun x => B x ν) x (ElasticityParameter.characteristicPlane ElasticityParameter.basis θ I)=
          connection θ hθ (t x) (fun i => q i x) (B x ν) := by
  sorry

end ElasticityFrame

end

end

end OAI
end
