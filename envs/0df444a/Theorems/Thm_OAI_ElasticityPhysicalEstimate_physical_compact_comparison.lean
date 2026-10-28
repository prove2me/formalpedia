-- Prove2me | Theorems.Thm_OAI_ElasticityPhysicalEstimate_physical_compact_comparison
-- name    : OAI.ElasticityPhysicalEstimate.physical_compact_comparison
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T10:46:51.888816+00:00
-- url     : https://prove2.me/theorems/70cf2e82-5a37-419b-a547-19efc009f4be
-- title:
--   OAI.ElasticityPhysicalEstimate.physical_compact_comparison: intermediate lemma from OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Elasticity.global_uniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem*, OpenAI Math Release, September 24, 2026, result family 372, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElasticityPhysicalEstimate.physical_compact_comparison` of [lean/OAI/MathematicalPhysics/Elasticity/Transfer.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/Transfer.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElasticityPhysicalEstimate`, with `open Set`, `open scoped BigOperators SchwartzMap`, `open ElasticityBessel ElasticitySchwartzCarleman ElasticityNegativeOrder ElasticityPhysicalAlgebra`, `open ElasticityAugmented (coord coeffA coeffV)`, `open ElasticityCoeffBounds`):
--
--   ```lean
--   theorem physical_compact_comparison {B K : Set X} (hB : IsOpen B)
--       (hK : IsClosed K) (hKB : K⊆B) (R : ℝ) (hR : 1≤R)
--       (hKR : K⊆Metric.closedBall 0 R) (α β : X) (hα : α≠0)
--       (lam m : Fin 2 → Smooth)
--       (hl : ∀ q,ExteriorConstant (lam q)) (hm : ∀ q,ExteriorConstant (m q))
--       (hm0 : ∀ q x,(m q : X → ℂ) x≠0)
--       (he0 : ∀ q x,((lam q+m q+m q : Smooth) : X → ℂ) x≠0)
--       (hel : EqOn (lam 0 : X → ℂ) (lam 1) Kᶜ)
--       (hem : EqOn (m 0 : X → ℂ) (m 1) Kᶜ) :
--       ∃ C h₀ : ℝ,0<C ∧ 0<h₀ ∧ ∀ h : ℝ,0<h → h≤h₀ →
--         ∀ u v : Fin 3 → S,
--         (∀ i,tsupport ((v-u) i : X → ℂ)⊆K) →
--         (∀ i,EqOn (physical (phase h α β) (lam 0) (m 0) u i : X → ℂ) 0 B) →
--         (∀ i,EqOn (physical (phase h α β) (lam 1) (m 1) v i : X → ℂ) 0 B) →
--         sobNorm h 1 (physicalAug (phase h α β) (v-u)) ≤
--           C*sobNorm h 1 (physicalAug (phase h α β) u)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElasticityAugmented.X`, `OAI.ElasticityBessel.S`, `OAI.ElasticityBessel.X` and `OAI.ElasticityPhysicalAlgebra.Smooth` (definitions bundle `OAIQ6El000` of this split); `OAI.ElasticityCoeffBounds.ExteriorConstant`, `OAI.ElasticityPhysicalAlgebra.phase` and `OAI.ElasticityPhysicalAlgebra.physical` (definitions bundle `OAIQ6El004` of this split); `OAI.ElasticityPhysicalEstimate.X` (definitions bundle `OAIQ6El005` of this split); `OAI.ElasticityNegativeOrder.sobNorm` and `OAI.ElasticityPhysicalEstimate.physicalAug` (definitions bundle `OAIQ6El006` of this split).
--
--   **Used by.** The proof of `OAI.Elasticity.dn_weak_transport_column` of this split imports it.
-- source:
--   OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 372; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/Transfer.lean (declaration OAI.ElasticityPhysicalEstimate.physical_compact_comparison)

import Mathlib
import Definitions.Def_OAIQ6El006

section

attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set
open scoped BigOperators SchwartzMap
namespace ElasticityPhysicalEstimate
open ElasticityBessel ElasticitySchwartzCarleman ElasticityNegativeOrder ElasticityPhysicalAlgebra
open ElasticityAugmented (coord coeffA coeffV)
open ElasticityCoeffBounds

theorem physical_compact_comparison {B K : Set X} (hB : IsOpen B)
    (hK : IsClosed K) (hKB : K⊆B) (R : ℝ) (hR : 1≤R)
    (hKR : K⊆Metric.closedBall 0 R) (α β : X) (hα : α≠0)
    (lam m : Fin 2 → Smooth)
    (hl : ∀ q,ExteriorConstant (lam q)) (hm : ∀ q,ExteriorConstant (m q))
    (hm0 : ∀ q x,(m q : X → ℂ) x≠0)
    (he0 : ∀ q x,((lam q+m q+m q : Smooth) : X → ℂ) x≠0)
    (hel : EqOn (lam 0 : X → ℂ) (lam 1) Kᶜ)
    (hem : EqOn (m 0 : X → ℂ) (m 1) Kᶜ) :
    ∃ C h₀ : ℝ,0<C ∧ 0<h₀ ∧ ∀ h : ℝ,0<h → h≤h₀ →
      ∀ u v : Fin 3 → S,
      (∀ i,tsupport ((v-u) i : X → ℂ)⊆K) →
      (∀ i,EqOn (physical (phase h α β) (lam 0) (m 0) u i : X → ℂ) 0 B) →
      (∀ i,EqOn (physical (phase h α β) (lam 1) (m 1) v i : X → ℂ) 0 B) →
      sobNorm h 1 (physicalAug (phase h α β) (v-u)) ≤
        C*sobNorm h 1 (physicalAug (phase h α β) u) := by
  sorry
end ElasticityPhysicalEstimate

end
end

end OAI
end
