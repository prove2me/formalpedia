-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_JumpFormula_multidimStochasticIntegral_rightCont_ae_eq
-- name    : LevyStochCalc.Ito.JumpFormula.multidimStochasticIntegral_rightCont_ae_eq
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T12:39:59.480536+00:00
-- url     : https://prove2.me/theorems/ac6054a3-ef9f-4c16-9837-9573e1deef03
-- title:
--   multidimStochasticIntegral rightCont ae eq
-- statement:
--   The source theorem `LevyStochCalc.Ito.JumpFormula.multidimStochasticIntegral_rightCont_ae_eq` is extracted from `LevyStochCalc.Ito.ItoLevyBoundedDerivsStepsIntegrands`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoLevyBoundedDerivsStepsIntegrands_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Admissibility of the mixed integrands of the Itô–Lévy formula

The mixed integrands of the Itô–Lévy formula along a jump diffusion — the derivatives of a `C²`
state function read at an auxiliary path, the coefficients read at the solution — are jointly
measurable, are progressively measurable for the right-continuous regularisation of the
filtration of the SDE data, and have finite energy on every bounded window; over that
regularisation the Brownian and the compensated jump integral agree almost surely with the ones
over the filtration itself, and the endpoint of a path together with its two stochastic
integrals is measurable componentwise.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open LevyStochCalc.Ito.Setting LevyStochCalc.Poisson.Compensated LevyStochCalc.Probability

namespace LevyStochCalc.Ito.JumpFormula

universe u v

section Mixed

open LevyStochCalc.Ito.BigJump LevyStochCalc.Brownian.Multidim LevyStochCalc.Brownian.Ito

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  {W : MultidimBrownianMotion P d} {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ} {X : JumpDiffusion W N coeffs x₀}
  {u : ℝ → (Fin n → ℝ) → ℝ}

theorem _root_.LevyStochCalc.Ito.JumpFormula.multidimStochasticIntegral_rightCont_ae_eq (S : SdeData X)
    (h𝒢W : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) S.ℱ.rightCont)
    (Z : ℝ → Ω → Fin d → ℝ)
    (hZm : ∀ j : Fin d, Measurable (Function.uncurry fun ω s => Z s ω j))
    (hZp : ∀ j : Fin d, Probability.ProgressivelyMeasurable S.ℱ fun ω s => Z s ω j)
    (hZp' : ∀ j : Fin d,
      Probability.ProgressivelyMeasurable S.ℱ.rightCont fun ω s => Z s ω j)
    (hZq : ∀ (j : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) (T : ℝ) :
    MultidimBrownianMotion.stochasticIntegral W S.ℱ.rightCont h𝒢W Z hZm hZp' hZq T
      =ᵐ[P] MultidimBrownianMotion.stochasticIntegral W S.ℱ S.isBrownian Z hZm hZp hZq T := by sorry
