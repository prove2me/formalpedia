-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_JumpFormula_ae_integrableOn_mixed_window
-- name    : LevyStochCalc.Ito.JumpFormula.ae_integrableOn_mixed_window
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T12:37:43.708519+00:00
-- url     : https://prove2.me/theorems/b13ffb78-a1ab-490d-bc53-06f3f5293134
-- title:
--   ae integrableOn mixed window
-- statement:
--   The source theorem `LevyStochCalc.Ito.JumpFormula.ae_integrableOn_mixed_window` is extracted from `LevyStochCalc.Ito.FiniteActivityMixedSteps`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_FiniteActivityMixedSteps_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Steps of the finite-activity Itô–Lévy identity in the mixed form

Regularity of the time-augmented path, window integrability of the mixed integrands, the
dictionary identifying the time-augmented drift and quadratic terms with the mixed drift
integrand, and the predictability and admissibility of the mixed jump increment read at the
left limits.

## Main statements

* `LevyStochCalc.Ito.JumpFormula.measurable_uncurry_timeAugProcess`
* `LevyStochCalc.Ito.JumpFormula.measurable_timeAugProcess_adapted`
* `LevyStochCalc.Ito.JumpFormula.tendsto_timeAugProcess_nhdsWithin_gt`
* `LevyStochCalc.Ito.JumpFormula.ae_integrableOn_mixed_window`
* `LevyStochCalc.Ito.JumpFormula.ae_setIntegral_timeAug_eq_mixedDrift`
* `LevyStochCalc.Ito.JumpFormula.admissible_mixedJumpIncrement_leftLim`
* `LevyStochCalc.Ito.JumpFormula.ae_countable_setOf_leftLim_ne_pair`
* `LevyStochCalc.Ito.JumpFormula.markedPredictable_zeroExtPos_mixedJumpIncrement_leftLim`
* `LevyStochCalc.Ito.JumpFormula.lintegral_referenceIntensity_window_ne_top`
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open LevyStochCalc.Ito.Setting LevyStochCalc.Poisson.Compensated LevyStochCalc.Probability
open LevyStochCalc.Brownian.Ito LevyStochCalc.Brownian.Multidim LevyStochCalc.Ito.BigJump
open LevyStochCalc.Ito.JumpSplitting

namespace LevyStochCalc.Ito.JumpFormula

universe u v

section TimeAug

variable {Ω : Type u} [MeasurableSpace Ω] {n : ℕ} {y : ℝ → Ω → Fin n → ℝ}

end TimeAug

section Mixed

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  {W : MultidimBrownianMotion P d} {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ} {X : JumpDiffusion W N coeffs x₀}

theorem _root_.LevyStochCalc.Ito.JumpFormula.ae_integrableOn_mixed_window (S : SdeData X)
    (hμm : ∀ i : Fin n, Measurable (Function.uncurry fun ω s => coeffs.μ s (X.X s ω) i))
    (hμq : ∀ (i : Fin n) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coeffs.μ s (X.X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hγmeas : Measurable fun q : ℝ × (Fin n → ℝ) × E => coeffs.γ q.1 q.2.1 q.2.2)
    (u : ℝ → (Fin n → ℝ) → ℝ) (hu : ContDiff ℝ 2 (Function.uncurry u))
    {K₀ K₁ K₂ : ℝ}
    (hK₀ : ∀ s x, |timeDeriv u s x| ≤ K₀)
    (hK₁ : ∀ s x i, |gradient u s x i| ≤ K₁)
    (hK₂ : ∀ s x i j, |hessian u s x i j| ≤ K₂)
    (T : ℝ) (hT : 0 < T)
    {B : Set E} (hBν : ν B ≠ ⊤)
    (y : ℝ → Ω → Fin n → ℝ) (hy_m : Measurable (Function.uncurry y)) :
    ∀ᵐ ω ∂P,
      (∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ i : Fin n,
        IntegrableOn (fun e => coeffs.γ s (X.X s ω) e i) B ν)
      ∧ (∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
        IntegrableOn (fun e => mixedJumpIncrement u coeffs.γ s (y s ω) (X.X s ω) e) B ν)
      ∧ IntegrableOn (fun s => ∫ e in B, mixedJumpIncrement u coeffs.γ s (y s ω) (X.X s ω) e ∂ν)
          (Set.Icc (0 : ℝ) T) volume
      ∧ IntegrableOn (fun s => ∑ i : Fin n,
          gradient u s (y s ω) i * ∫ e in B, coeffs.γ s (X.X s ω) e i ∂ν)
          (Set.Icc (0 : ℝ) T) volume
      ∧ IntegrableOn (fun s => mixedDriftIntegrand u coeffs s (y s ω) (X.X s ω))
          (Set.Icc (0 : ℝ) T) volume := by sorry
