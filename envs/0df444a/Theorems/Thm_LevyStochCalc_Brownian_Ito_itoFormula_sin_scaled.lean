-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_itoFormula_sin_scaled
-- name    : LevyStochCalc.Brownian.Ito.itoFormula_sin_scaled
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:43:17.361807+00:00
-- url     : https://prove2.me/theorems/b16dc77a-642f-4621-a13a-ad319194435b
-- title:
--   itoFormula sin scaled
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.itoFormula_sin_scaled` is extracted from `LevyStochCalc.Brownian.ItoTrigIncrement`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Analysis_ScaledTrig_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoFormulaScalar_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoFormulaScalar_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoIncrement_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Itô's formula for the scaled cosine and sine of a Brownian increment

`x ↦ cos (l * x)` and `x ↦ sin (l * x)` satisfy the hypotheses of Itô's formula for a scalar Itô
process, so for a version of `∫ 1_{(a,b]} dW` they give

  `cos (l * X_T) − cos (l * X_0) = ∫ (−l sin (l X)) 1_{(a,b]} dW − (l²/2) ∫ cos (l X) 1_{(a,b]} ds`

and the companion identity for the sine.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

section Trig

variable {P : Measure Ω} [IsProbabilityMeasure P] {W : LevyStochCalc.Brownian.BrownianMotion P}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {hℱ : IsBrownianFiltration W ℱ}
  {a b : ℝ}
  {hm : Measurable (Function.uncurry (indIoc Ω a b))}
  {hp : Probability.ProgressivelyMeasurable ℱ (indIoc Ω a b)}
  {hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X : ℝ → Ω → ℝ}

variable (hC0 : (0 : ℝ) ≤ 1) (hCH : ∀ (ω : Ω) (s : ℝ), |indIoc Ω a b ω s| ≤ 1)

include hℱ hC0 hCH in

theorem _root_.LevyStochCalc.Brownian.Ito.itoFormula_sin_scaled
    (hX : IsItoVersion W ℱ hℱ (indIoc Ω a b) hm hp hq (fun _ => 0) (fun _ _ => 0) X) (l : ℝ)
    (hmg : Measurable (Function.uncurry fun ω s =>
      (l * Real.cos (l * X s ω)) * indIoc Ω a b ω s))
    (hpg : Probability.ProgressivelyMeasurable ℱ fun ω s =>
      (l * Real.cos (l * X s ω)) * indIoc Ω a b ω s)
    (hqg : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖(l * Real.cos (l * X s ω)) * indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    (fun ω : Ω => Real.sin (l * X T ω) - Real.sin (l * X 0 ω)) =ᵐ[P] fun ω =>
      stochasticIntegralBrownian W ℱ hℱ
          (fun ω s => (l * Real.cos (l * X s ω)) * indIoc Ω a b ω s) hmg hpg hqg T ω
        + 1 / 2 * ∫ s in Set.Ioc (0 : ℝ) T,
            (-l ^ 2 * Real.sin (l * X s ω)) * indIoc Ω a b ω s ^ 2 ∂volume := by sorry
