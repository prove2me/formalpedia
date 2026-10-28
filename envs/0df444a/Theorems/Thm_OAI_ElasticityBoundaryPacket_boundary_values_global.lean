-- Prove2me | Theorems.Thm_OAI_ElasticityBoundaryPacket_boundary_values_global
-- name    : OAI.ElasticityBoundaryPacket.boundary_values_global
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T10:28:07.142184+00:00
-- url     : https://prove2.me/theorems/28d60061-8239-4195-ba0c-4553b9a581f8
-- title:
--   OAI.ElasticityBoundaryPacket.boundary_values_global: intermediate lemma from OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Elasticity.global_uniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem*, OpenAI Math Release, September 24, 2026, result family 372, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElasticityBoundaryPacket.boundary_values_global` of [lean/OAI/MathematicalPhysics/Elasticity/BoundaryValues.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/BoundaryValues.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElasticityBoundaryPacket`, with `open Set`, `open scoped Topology BigOperators`, `open Elasticity ElasticityBoundaryLayerOperator`):
--
--   ```lean
--   lemma boundary_values_global {l₁ m₁ l₂ m₂ : X → ℝ}
--       (hS : SourceSmoothBoundary Ω) (hO : IsOpen Ω) (hB : Bornology.IsBounded Ω)
--       (hl₁ : ContDiff ℝ (⊤ : ℕ∞) l₁) (hm₁ : ContDiff ℝ (⊤ : ℕ∞) m₁)
--       (hl₂ : ContDiff ℝ (⊤ : ℕ∞) l₂) (hm₂ : ContDiff ℝ (⊤ : ℕ∞) m₂)
--       (ha₁ : Admissible Ω l₁ m₁) (ha₂ : Admissible Ω l₂ m₂)
--       (hDN : DN Ω l₁ m₁=DN Ω l₂ m₂) (hx : x∈frontier Ω) : l₁ x=l₂ x ∧ m₁ x=m₂ x
--   ```
--
--   **Definitions.** The statement is written with `OAI.Elasticity.SourceSmoothBoundary` (definitions bundle `OAIQ6El000` of this split); `OAI.ElasticityBoundaryPacket.I` and `OAI.ElasticityBoundaryPacket.X` (definitions bundle `OAIQ6El001` of this split); `OAI.Elasticity.Admissible`, `OAI.Elasticity.BoundaryData` and `OAI.Elasticity.DN` (the published bundle `Def_ElasticityUniqueness`).
--
--   **Used by.** The proof of `OAI.ElasticityBoundaryPacket.boundary_jets_global` of this split imports it.
-- source:
--   OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 372; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/BoundaryValues.lean (declaration OAI.ElasticityBoundaryPacket.boundary_values_global)

import Mathlib
import Definitions.Def_ElasticityUniqueness
import Definitions.Def_OAIQ6El000
import Definitions.Def_OAIQ6El001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set
open scoped Topology BigOperators
namespace ElasticityBoundaryPacket
open Elasticity ElasticityBoundaryLayerOperator
variable {Ω : Set X} {x : X}

lemma boundary_values_global {l₁ m₁ l₂ m₂ : X → ℝ}
    (hS : SourceSmoothBoundary Ω) (hO : IsOpen Ω) (hB : Bornology.IsBounded Ω)
    (hl₁ : ContDiff ℝ (⊤ : ℕ∞) l₁) (hm₁ : ContDiff ℝ (⊤ : ℕ∞) m₁)
    (hl₂ : ContDiff ℝ (⊤ : ℕ∞) l₂) (hm₂ : ContDiff ℝ (⊤ : ℕ∞) m₂)
    (ha₁ : Admissible Ω l₁ m₁) (ha₂ : Admissible Ω l₂ m₂)
    (hDN : DN Ω l₁ m₁=DN Ω l₂ m₂) (hx : x∈frontier Ω) : l₁ x=l₂ x ∧ m₁ x=m₂ x := by
  sorry

end ElasticityBoundaryPacket

end
end

end OAI
end
