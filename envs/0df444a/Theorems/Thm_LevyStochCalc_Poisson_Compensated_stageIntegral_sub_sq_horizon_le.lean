-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_Compensated_stageIntegral_sub_sq_horizon_le
-- name    : LevyStochCalc.Poisson.Compensated.stageIntegral_sub_sq_horizon_le
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T15:51:03.388739+00:00
-- url     : https://prove2.me/theorems/8e5b3b6f-6ae7-45ca-8e9e-e71b06645c70
-- title:
--   stageIntegral sub sq horizon le
-- statement:
--   The source theorem `LevyStochCalc.Poisson.Compensated.stageIntegral_sub_sq_horizon_le` is extracted from `LevyStochCalc.Poisson.CompensatedApprox`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedApprox_F001
import Definitions.Def_LevyStochCalc_Poisson_MarkStepIncrement_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Approximation of a square-integrable integrand by mark-step integrands

For a jointly measurable, progressively measurable integrand `φ : Ω → ℝ → E → ℝ` that is
square integrable over `Ω × [0, T] × E`, and any dyadic level `L₀` and tolerance `ε`, there is
an adapted mark-step integrand on a dyadic grid of level at least `L₀` within `ε` of `φ` in
`L²(P ⊗ ds ⊗ ν)` on `[0, T]` (`exists_markStep_close`). The integrand is first clipped and
restricted to a mark set of finite measure (`truncate`), which reduces to the bounded,
finitely supported case treated by `exists_markEval_L2_tendsto`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

section Truncate

variable (φ : Ω → ℝ → E → ℝ) (M : ℝ) (S : Set E)

variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

end Truncate

section Close

variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  (N : PoissonRandomMeasure P ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration
    N ℱ)
  (φ : Ω → ℝ → E → ℝ)
  (h_meas : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
  (h_progMeas : Probability.MarkedProgressivelyMeasurable ℱ φ)

end Close

section Master

variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  (N : PoissonRandomMeasure P ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration
    N ℱ)
  (φ : Ω → ℝ → E → ℝ)
  (h_meas : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
  (h_progMeas : Probability.MarkedProgressivelyMeasurable ℱ φ)
  (h_sq_int_global : ∀ T : ℝ, 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

end Master

section Cauchy

variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  (N : PoissonRandomMeasure P ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration
    N ℱ)
  (φ : Ω → ℝ → E → ℝ)
  (h_meas : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
  (h_progMeas : Probability.MarkedProgressivelyMeasurable ℱ φ)
  (h_sq_int_global : ∀ T : ℝ, 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

include hℱ in

theorem _root_.LevyStochCalc.Poisson.Compensated.stageIntegral_sub_sq_horizon_le {n n' : ℕ} (h : n ≤ n') :
    ∫⁻ ω, (‖stageIntegral N ℱ φ h_meas h_progMeas h_sq_int_global n (stageHorizon n) ω
        - stageIntegral N ℱ φ h_meas h_progMeas h_sq_int_global n' (stageHorizon n) ω‖₊
          : ℝ≥0∞) ^ 2 ∂P
      ≤ 2 * ((n : ℝ≥0∞) + 1)⁻¹ + 2 * ((n' : ℝ≥0∞) + 1)⁻¹ := by sorry
