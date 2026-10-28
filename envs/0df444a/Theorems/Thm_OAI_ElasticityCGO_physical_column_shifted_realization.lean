-- Prove2me | Theorems.Thm_OAI_ElasticityCGO_physical_column_shifted_realization
-- name    : OAI.ElasticityCGO.physical_column_shifted_realization
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T10:44:20.668599+00:00
-- url     : https://prove2.me/theorems/8a9f2152-efda-4359-8ab5-7262a5d2e139
-- title:
--   OAI.ElasticityCGO.physical_column_shifted_realization: intermediate lemma from OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Elasticity.global_uniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem*, OpenAI Math Release, September 24, 2026, result family 372, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElasticityCGO.physical_column_shifted_realization` of [lean/OAI/MathematicalPhysics/Elasticity/PhysicalCGO.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/PhysicalCGO.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElasticityCGO`, with `open Set MeasureTheory TemperedDistribution`, `open scoped SchwartzMap ENNReal BigOperators`, `open ElasticityAugmented`, `open ElasticityCoeffBounds (ExteriorConstant)`, `open ElasticityPhysicalAlgebra (phase physical)`, `open ElasticityPhysicalEstimate (physicalAug)`, `open ElasticityNegativeOrder (mult sobNorm)`, `open ElasticityRegularity (sobolevInjection)`, `open ElasticityDistribution (HV Dist divd)`):
--
--   ```lean
--   theorem physical_column_shifted_realization (R : ℝ) (hR : 1≤R) (α β : X)
--       (lam m : Smooth)
--       (a : ℕ → Amplitude Smooth) (ha : PhysicalColumn R hR α β lam m a)
--       {g : X → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g)
--       (hs : tsupport g⊆Metric.ball 0 R) :
--       ∃ C h₀ : ℝ,0<C ∧ 0<h₀ ∧ h₀≤1 ∧ ∀ h : ℝ,0<h → h≤h₀ →
--         ∃ w : ElasticityPhysicalDual.H,∃ q : HV,∃ v : Fin 3 → S,
--           (∀ i,∀ᵐ x ∂(volume : Measure X),x∈Metric.ball 0 R → w i x=v i x) ∧
--           (∀ i,EqOn (physical (phase h α β) lam m
--             ((fun j => cut ⟨fiveCutoff R hR 0,fiveCutoff_smooth R hR 0⟩ (fiveCutoff_compact R hR 0)
--               ((truncation (h : ℂ) 8 a).1 j))-v) i : X → ℂ) 0 (Metric.ball 0 R)) ∧
--           (∀ i,sobolevInjection 1 (q i)=smulLeftCLM ℂ (fiveCutoff R hR 0)
--             ((Fin.cons (divd (phase h α β) (fun j => (w j : Dist)))
--               (fun j => (w j : Dist)) : Fin 4 → Dist) i)) ∧
--           ‖w‖≤C*h^7 ∧ ‖q‖≤C*h ∧
--           sobNorm h 1 (physicalAug (phase h α β) (fun i => mult g (v i)))≤C*h
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElasticityAugmented.Amplitude`, `OAI.ElasticityAugmented.Smooth`, `OAI.ElasticityAugmented.X`, `OAI.ElasticityBessel.S`, `OAI.ElasticityBessel.X`, `OAI.ElasticityCGO.S`, `OAI.ElasticityDistribution.Dist`, `OAI.ElasticityDistribution.X`, `OAI.ElasticityPhysicalDual.H` and `OAI.ElasticityPhysicalDual.X` (definitions bundle `OAIQ6El000` of this split); `OAI.ElasticityAugmented.truncation` (definitions bundle `OAIQ6El001` of this split); `OAI.ElasticityRegularity.sobolevInjection` (definitions bundle `OAIQ6El002` of this split); `OAI.ElasticityCGO.PhysicalColumn`, `OAI.ElasticityCGO.cut`, `OAI.ElasticityCGO.fiveCutoff`, `OAI.ElasticityCGO.fiveCutoff_compact`, `OAI.ElasticityCGO.fiveCutoff_smooth`, `OAI.ElasticityDistribution.H`, `OAI.ElasticityDistribution.HV`, `OAI.ElasticityDistribution.divd`, `OAI.ElasticityNegativeOrder.mult`, `OAI.ElasticityPhysicalAlgebra.phase` and `OAI.ElasticityPhysicalAlgebra.physical` (definitions bundle `OAIQ6El004` of this split); `OAI.ElasticityNegativeOrder.sobNorm` and `OAI.ElasticityPhysicalEstimate.physicalAug` (definitions bundle `OAIQ6El006` of this split).
--
--   **Used by.** The proof of `OAI.ElasticityCGO.localized_actual_strong_bound` of this split imports it.
-- source:
--   OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 372; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/PhysicalCGO.lean (declaration OAI.ElasticityCGO.physical_column_shifted_realization)

import Mathlib
import Definitions.Def_OAIQ6El006

section

attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityCGO
open Set MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal BigOperators
open ElasticityAugmented
open ElasticityCoeffBounds (ExteriorConstant)
open ElasticityPhysicalAlgebra (phase physical)
open ElasticityPhysicalEstimate (physicalAug)
open ElasticityNegativeOrder (mult sobNorm)
open ElasticityRegularity (sobolevInjection)
open ElasticityDistribution (HV Dist divd)

theorem physical_column_shifted_realization (R : ℝ) (hR : 1≤R) (α β : X)
    (lam m : Smooth)
    (a : ℕ → Amplitude Smooth) (ha : PhysicalColumn R hR α β lam m a)
    {g : X → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g)
    (hs : tsupport g⊆Metric.ball 0 R) :
    ∃ C h₀ : ℝ,0<C ∧ 0<h₀ ∧ h₀≤1 ∧ ∀ h : ℝ,0<h → h≤h₀ →
      ∃ w : ElasticityPhysicalDual.H,∃ q : HV,∃ v : Fin 3 → S,
        (∀ i,∀ᵐ x ∂(volume : Measure X),x∈Metric.ball 0 R → w i x=v i x) ∧
        (∀ i,EqOn (physical (phase h α β) lam m
          ((fun j => cut ⟨fiveCutoff R hR 0,fiveCutoff_smooth R hR 0⟩ (fiveCutoff_compact R hR 0)
            ((truncation (h : ℂ) 8 a).1 j))-v) i : X → ℂ) 0 (Metric.ball 0 R)) ∧
        (∀ i,sobolevInjection 1 (q i)=smulLeftCLM ℂ (fiveCutoff R hR 0)
          ((Fin.cons (divd (phase h α β) (fun j => (w j : Dist)))
            (fun j => (w j : Dist)) : Fin 4 → Dist) i)) ∧
        ‖w‖≤C*h^7 ∧ ‖q‖≤C*h ∧
        sobNorm h 1 (physicalAug (phase h α β) (fun i => mult g (v i)))≤C*h := by
  sorry
end ElasticityCGO

end

end OAI
end
