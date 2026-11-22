-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_JumpFormula_measurable_compensatorDriftIntegrand_path_c12
-- name    : LevyStochCalc.Ito.JumpFormula.measurable_compensatorDriftIntegrand_path_c12
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T13:01:31.909948+00:00
-- url     : https://prove2.me/theorems/14b62b26-2847-4222-9282-de72411a1b35
-- title:
--   measurable compensatorDriftIntegrand path c12
-- statement:
--   The source theorem `LevyStochCalc.Ito.JumpFormula.measurable_compensatorDriftIntegrand_path_c12` is extracted from `LevyStochCalc.Ito.ItoLevyBoundedDerivsSolutionIntegrandsC12`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoLevyBoundedDerivsSolutionIntegrandsC12_F000

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

omit [IsProbabilityMeasure P] [SigmaFinite ν] in

theorem _root_.LevyStochCalc.Ito.JumpFormula.measurable_compensatorDriftIntegrand_path_c12 (hu : IsC12 u)
    (hγ : Measurable fun q : ℝ × (Fin n → ℝ) × E => coeffs.γ q.1 q.2.1 q.2.2)
    (hXm : Measurable (Function.uncurry X)) :
    Measurable fun p : Ω × ℝ × E =>
      compensatorDriftIntegrand u coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 := by sorry
