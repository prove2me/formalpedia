-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_JumpFormula_ae_setIntegral_timeAug_eq_mixedDrift
-- name    : LevyStochCalc.Ito.JumpFormula.ae_setIntegral_timeAug_eq_mixedDrift
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T12:37:57.574456+00:00
-- url     : https://prove2.me/theorems/ce4471eb-1d8b-4ef3-9261-32bd30b1293e
-- title:
--   ae setIntegral timeAug eq mixedDrift
-- statement:
--   The source theorem `LevyStochCalc.Ito.JumpFormula.ae_setIntegral_timeAug_eq_mixedDrift` is extracted from `LevyStochCalc.Ito.FiniteActivityMixedSteps`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_FiniteActivityMixedPrelims_F000
import Definitions.Def_LevyStochCalc_Ito_FiniteActivityMixedPrelims_F001
import Definitions.Def_LevyStochCalc_Ito_ItoFormulaMeasurableShift_F000
import Definitions.Def_LevyStochCalc_Ito_ItoLevyMixedBounds_F001
import Definitions.Def_LevyStochCalc_Ito_JumpFormulaChainStopped_F000
import Definitions.Def_LevyStochCalc_Probability_MarkedPredictableComp_F000
import Definitions.Def_LevyStochCalc_Probability_MarkedPredictableComp_F001

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

theorem _root_.LevyStochCalc.Ito.JumpFormula.ae_setIntegral_timeAug_eq_mixedDrift
    {f : (Fin (n + 1) → ℝ) → ℝ}
    {f' : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] ℝ}
    {f'' : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) →L[ℝ] ℝ}
    {u : ℝ → (Fin n → ℝ) → ℝ} (hfu : ∀ z, f z = timeAugFun u z)
    (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    (B : Set E) (T : ℝ) (hT : 0 < T) (y : ℝ → Ω → Fin n → ℝ)
    (bdr : Fin n → Ω → ℝ → ℝ)
    (hbdr : ∀ (i : Fin n) (ω : Ω) (s : ℝ),
      bdr i ω s = continuousDriftLeftAt coeffs ν X.X B i ω s)
    (H : Fin n → Fin d → Ω → ℝ → ℝ)
    (hH : ∀ (i : Fin n) (j : Fin d) (ω : Ω) (s : ℝ), H i j ω s = coeffs.σ s (X.X s ω) i j)
    (hmD : ∀ p : Fin (n + 1), Measurable (Function.uncurry
      fun ω s => coordDeriv f' p (timeAugProcess y s ω) * timeAugDrift bdr p ω s))
    (hqD : ∀ (p : Fin (n + 1)) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖coordDeriv f' p (timeAugProcess y s ω) * timeAugDrift bdr p ω s‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P < ⊤)
    (hQint : ∀ᵐ ω ∂P, ∀ p q : Fin (n + 1), IntegrableOn
      (fun s => coordDeriv₂ f'' p q (timeAugProcess y s ω)
        * ∑ j : Fin d, timeAugDiffusion H p j ω s * timeAugDiffusion H q j ω s)
      (Set.Ioc (0 : ℝ) T) volume) :
    ∀ᵐ ω ∂P, (∑ p : Fin (n + 1), ∫ s in Set.Ioc (0 : ℝ) T,
          coordDeriv f' p (timeAugProcess y s ω) * timeAugDrift bdr p ω s ∂volume)
        + 1 / 2 * ∑ p : Fin (n + 1), ∑ q : Fin (n + 1), ∫ s in Set.Ioc (0 : ℝ) T,
            coordDeriv₂ f'' p q (timeAugProcess y s ω)
              * (∑ j : Fin d, timeAugDiffusion H p j ω s * timeAugDiffusion H q j ω s) ∂volume
      = ∫ s in Set.Icc (0 : ℝ) T, (mixedDriftIntegrand u coeffs s (y s ω) (X.X s ω)
          - ∑ i : Fin n, gradient u s (y s ω) i * ∫ e in B, coeffs.γ s (X.X s ω) e i ∂ν) := by sorry
