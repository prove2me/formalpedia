-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_JumpFormula_ae_lintegral_compensatorDriftIntegrand_lt_top
-- name    : LevyStochCalc.Ito.JumpFormula.ae_lintegral_compensatorDriftIntegrand_lt_top
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T12:45:02.762416+00:00
-- url     : https://prove2.me/theorems/afa36c31-c66f-4d0c-ac51-78c6c727b041
-- title:
--   ae lintegral compensatorDriftIntegrand lt top
-- statement:
--   The source theorem `LevyStochCalc.Ito.JumpFormula.ae_lintegral_compensatorDriftIntegrand_lt_top` is extracted from `LevyStochCalc.Ito.ItoLevyBoundedDerivsSolutionIntegrands`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoLevyBoundedDerivs_F000
import Definitions.Def_LevyStochCalc_Ito_PicardWellPosed_F000
import Definitions.Def_LevyStochCalc_Ito_SdeDataOfSolvesOn_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Admissibility of the derived integrands along a path

The two stochastic integrals of the Itô–Lévy formula at bounded derivatives carry the integrands
`(∇u)ᵀσ` and `u(x + γ) − u(x)` evaluated along a path. For a `C²` state function with bounded
gradient and coefficients that are regular and Lipschitz, each of these is jointly measurable,
progressively measurable in the sense its integral asks for, and of finite energy on every
window; along the path the drift is integrable and the compensator-drift integrand has finite
mark energy, almost surely.
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

theorem _root_.LevyStochCalc.Ito.JumpFormula.ae_lintegral_compensatorDriftIntegrand_lt_top (hu : ContDiff ℝ 2 (Function.uncurry u))
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
