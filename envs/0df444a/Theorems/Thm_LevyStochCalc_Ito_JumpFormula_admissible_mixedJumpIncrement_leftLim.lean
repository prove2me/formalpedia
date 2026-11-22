-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_JumpFormula_admissible_mixedJumpIncrement_leftLim
-- name    : LevyStochCalc.Ito.JumpFormula.admissible_mixedJumpIncrement_leftLim
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T12:28:37.096738+00:00
-- url     : https://prove2.me/theorems/ce182a56-2fd0-48b7-b4e7-f720e16a07af
-- title:
--   admissible mixedJumpIncrement leftLim
-- statement:
--   The source theorem `LevyStochCalc.Ito.JumpFormula.admissible_mixedJumpIncrement_leftLim` is extracted from `LevyStochCalc.Ito.FiniteActivityMixedSteps`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
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

theorem _root_.LevyStochCalc.Ito.JumpFormula.admissible_mixedJumpIncrement_leftLim (S : SdeData X)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → S.ℱ 0 ≤ S.ℱ t)
    {u : ℝ → (Fin n → ℝ) → ℝ} (hu : ContDiff ℝ 2 (Function.uncurry u))
    {K₁ : ℝ} (hK₁ : ∀ s x i, |gradient u s x i| ≤ K₁)
    {y : ℝ → Ω → Fin n → ℝ} (hy_m : Measurable (Function.uncurry y))
    (hy_ad : ∀ t : ℝ, Measurable[S.ℱ t] (y t))
    (hy_left : ∀ (ω : Ω) (t : ℝ) (j : Fin n),
      ∃ L : ℝ, Tendsto (fun s => y s ω j) (𝓝[<] t) (𝓝 L))
    (hγmL : ∀ i : Fin n, Measurable fun p : Ω × ℝ × E =>
      coeffs.γ p.2.1 (leftLimPathAt X.X p.2.1 p.1) p.2.2 i)
    (hγpL : ∀ i : Fin n, Probability.MarkedProgressivelyMeasurable S.ℱ
      fun ω s e => coeffs.γ s (leftLimPathAt X.X s ω) e i)
    (hγqL : ∀ (i : Fin n) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖coeffs.γ s (leftLimPathAt X.X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) :
    Measurable (fun p : Ω × ℝ × E => mixedJumpIncrement u coeffs.γ p.2.1
        (leftLimPathAt y p.2.1 p.1) (leftLimPathAt X.X p.2.1 p.1) p.2.2)
      ∧ Probability.MarkedProgressivelyMeasurable S.ℱ (fun ω s e =>
          mixedJumpIncrement u coeffs.γ s (leftLimPathAt y s ω) (leftLimPathAt X.X s ω) e)
      ∧ ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
          (‖mixedJumpIncrement u coeffs.γ s (leftLimPathAt y s ω)
            (leftLimPathAt X.X s ω) e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ := by sorry
