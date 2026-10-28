-- Prove2me | Theorems.Thm_OAI_ElasticityCGO_localized_actual_strong_bound
-- name    : OAI.ElasticityCGO.localized_actual_strong_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T10:43:27.502616+00:00
-- url     : https://prove2.me/theorems/8387613b-3ecd-4094-bfc3-7aaa626c6bd5
-- title:
--   OAI.ElasticityCGO.localized_actual_strong_bound: intermediate lemma from OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Elasticity.global_uniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem*, OpenAI Math Release, September 24, 2026, result family 372, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElasticityCGO.localized_actual_strong_bound` of [lean/OAI/MathematicalPhysics/Elasticity/WeakLimits.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/WeakLimits.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElasticityCGO`, with `open Set MeasureTheory Filter`, `open scoped SchwartzMap Topology BigOperators`, `open ElasticityAugmented`, `open ElasticityCoeffBounds (ExteriorConstant)`, `open ElasticityBessel (L2 norm2)`, `open ElasticityNegativeOrder (mult sobNorm)`, `open ElasticityPhysicalAlgebra (phase physical)`, `open ElasticityPhysicalEstimate (physicalAug)`):
--
--   ```lean
--   theorem localized_actual_strong_bound (R : ℝ) (hR : 1≤R) (α β : X)
--       (lam m : Smooth) (hl : ExteriorConstant lam) (hm : ExteriorConstant m)
--       (a : ℕ → Amplitude Smooth) (ha : PhysicalColumn R hR α β lam m a)
--       (h₀ : normal (fun i => (α i : ℂ)+Complex.I*(β i : ℂ)) (a 0).1=0)
--       (hrec : ∀ j<8,EqOn (fun x => ((normal (fun i => (α i : ℂ)+Complex.I*(β i : ℂ))
--         (a (j+1)).1 : Smooth) : X → ℂ) x)
--         (fun x => ((-(div coord (a j).1-(a j).2) : Smooth) : X → ℂ) x) (Metric.ball 0 R))
--       {g : X → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g)
--       (hs : tsupport g⊆Metric.ball 0 R) {B : Set X} (hB : IsOpen B)
--       (hBR : B⊆Metric.ball 0 R) (hg1 : EqOn g 1 B) :
--       ∃ C D h₁ : ℝ,0<C ∧ 0<D ∧ 0<h₁ ∧ ∀ h : ℝ,0<h → h≤h₁ → ∃ u : Fin 3 → S,
--         (∀ i,EqOn (physical (phase h α β) lam m u i : X → ℂ) 0 B) ∧
--         sobNorm h 1 (physicalAug (phase h α β) u)≤C ∧
--         ∀ i,‖L2 (physicalAug (phase h α β) u i-
--           physicalAug (phase h α β) (localizedFormal R hR (h : ℂ) a g) i)‖≤D*h
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElasticityAugmented.Amplitude`, `OAI.ElasticityAugmented.Smooth`, `OAI.ElasticityAugmented.X`, `OAI.ElasticityAugmented.coord`, `OAI.ElasticityAugmented.div`, `OAI.ElasticityAugmented.normal`, `OAI.ElasticityBessel.S`, `OAI.ElasticityBessel.X` and `OAI.ElasticityCGO.S` (definitions bundle `OAIQ6El000` of this split); `OAI.ElasticityBessel.L2`, `OAI.ElasticityCGO.PhysicalColumn`, `OAI.ElasticityCGO.localizedFormal`, `OAI.ElasticityCoeffBounds.ExteriorConstant`, `OAI.ElasticityPhysicalAlgebra.phase` and `OAI.ElasticityPhysicalAlgebra.physical` (definitions bundle `OAIQ6El004` of this split); `OAI.ElasticityNegativeOrder.sobNorm` and `OAI.ElasticityPhysicalEstimate.physicalAug` (definitions bundle `OAIQ6El006` of this split).
--
--   **Used by.** The proof of `OAI.Elasticity.dn_weak_transport_column` of this split imports it.
-- source:
--   OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 372; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/WeakLimits.lean (declaration OAI.ElasticityCGO.localized_actual_strong_bound)

import Mathlib
import Definitions.Def_OAIQ6El006

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityCGO

open Set MeasureTheory Filter
open scoped SchwartzMap Topology BigOperators
open ElasticityAugmented
open ElasticityCoeffBounds (ExteriorConstant)
open ElasticityBessel (L2 norm2)
open ElasticityNegativeOrder (mult sobNorm)
open ElasticityPhysicalAlgebra (phase physical)
open ElasticityPhysicalEstimate (physicalAug)

theorem localized_actual_strong_bound (R : ℝ) (hR : 1≤R) (α β : X)
    (lam m : Smooth) (hl : ExteriorConstant lam) (hm : ExteriorConstant m)
    (a : ℕ → Amplitude Smooth) (ha : PhysicalColumn R hR α β lam m a)
    (h₀ : normal (fun i => (α i : ℂ)+Complex.I*(β i : ℂ)) (a 0).1=0)
    (hrec : ∀ j<8,EqOn (fun x => ((normal (fun i => (α i : ℂ)+Complex.I*(β i : ℂ))
      (a (j+1)).1 : Smooth) : X → ℂ) x)
      (fun x => ((-(div coord (a j).1-(a j).2) : Smooth) : X → ℂ) x) (Metric.ball 0 R))
    {g : X → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g)
    (hs : tsupport g⊆Metric.ball 0 R) {B : Set X} (hB : IsOpen B)
    (hBR : B⊆Metric.ball 0 R) (hg1 : EqOn g 1 B) :
    ∃ C D h₁ : ℝ,0<C ∧ 0<D ∧ 0<h₁ ∧ ∀ h : ℝ,0<h → h≤h₁ → ∃ u : Fin 3 → S,
      (∀ i,EqOn (physical (phase h α β) lam m u i : X → ℂ) 0 B) ∧
      sobNorm h 1 (physicalAug (phase h α β) u)≤C ∧
      ∀ i,‖L2 (physicalAug (phase h α β) u i-
        physicalAug (phase h α β) (localizedFormal R hR (h : ℂ) a g) i)‖≤D*h := by
  sorry

end ElasticityCGO

end

end OAI
end
