-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_JumpFormula_ae_lintegral_compensatorDriftIntegrand_lt_top_c12
-- name    : LevyStochCalc.Ito.JumpFormula.ae_lintegral_compensatorDriftIntegrand_lt_top_c12
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T12:48:24.470126+00:00
-- url     : https://prove2.me/theorems/3839471a-d4cb-4ce3-a996-0d816ddcda06
-- title:
--   ae lintegral compensatorDriftIntegrand lt top c12
-- statement:
--   The source theorem `LevyStochCalc.Ito.JumpFormula.ae_lintegral_compensatorDriftIntegrand_lt_top_c12` is extracted from `LevyStochCalc.Ito.ItoLevyBoundedDerivsSolutionIntegrandsC12`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoLevyBoundedDerivsSolutionIntegrands_F000
import Definitions.Def_LevyStochCalc_Ito_JumpFormulaContinuityC12_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Admissibility of the derived integrands of a `C^{1,2}` state function along a path

The two stochastic integrals of the Itô–Lévy formula carry the integrands `(∇u)ᵀσ` and
`u(x + γ) − u(x)` evaluated along a path. For a state function of class `C^{1,2}` with bounded
gradient and jointly measurable coefficients, each of these is jointly measurable, progressively
measurable in the sense its integral asks for, and of finite energy on every window on which the
coefficient along the path has; the compensator-drift integrand is jointly measurable and, for a
bounded Hessian, has finite mark energy on a window, almost surely.

## Main statements

* `LevyStochCalc.Ito.JumpFormula.measurable_diffusionIntegrand_path_c12`,
  `LevyStochCalc.Ito.JumpFormula.progressivelyMeasurable_diffusionIntegrand_path_c12` — the
  admissibility of `(∇u)ᵀσ` along the path.
* `LevyStochCalc.Ito.JumpFormula.measurable_jumpIncrement_path_c12`,
  `LevyStochCalc.Ito.JumpFormula.markedProgressivelyMeasurable_jumpIncrement_path_c12`,
  `LevyStochCalc.Ito.JumpFormula.lintegral_sq_jumpIncrement_path_lt_top_c12` — the admissibility
  of `u(x + γ) − u(x)` along the path.
* `LevyStochCalc.Ito.JumpFormula.measurable_compensatorDriftIntegrand_path_c12`,
  `LevyStochCalc.Ito.JumpFormula.ae_lintegral_compensatorDriftIntegrand_lt_top_c12` — the
  measurability and the mark integrability of the compensator-drift integrand along the path.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.JumpFormula

open LevyStochCalc.Ito.Setting LevyStochCalc.Ito.Picard LevyStochCalc.Ito.BigJump
  LevyStochCalc.Probability

universe u v

section DerivedIntegrands

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  {coeffs : JumpDiffusionCoeffs n d E} {u : ℝ → (Fin n → ℝ) → ℝ}
  {X : ℝ → Ω → Fin n → ℝ}

omit [IsProbabilityMeasure P] in

theorem _root_.LevyStochCalc.Ito.JumpFormula.ae_lintegral_compensatorDriftIntegrand_lt_top_c12 (hu : IsC12 u)
    {K₂ : ℝ} (hK₂ : ∀ s x i j, |hessian u s x i j| ≤ K₂)
    (hγ : Measurable fun q : ℝ × (Fin n → ℝ) × E => coeffs.γ q.1 q.2.1 q.2.2)
    (hXm : Measurable (Function.uncurry X))
    (hγm : ∀ i : Fin n, Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i)
    (hγq : ∀ i : Fin n, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
        (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂P, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖compensatorDriftIntegrand u coeffs.γ s (X s ω) e‖₊ : ℝ≥0∞) ∂ν ∂volume < ⊤ := by sorry
