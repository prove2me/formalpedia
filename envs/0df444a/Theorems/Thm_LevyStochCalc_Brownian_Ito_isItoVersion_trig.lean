-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_isItoVersion_trig
-- name    : LevyStochCalc.Brownian.Ito.isItoVersion_trig
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:56:51.83051+00:00
-- url     : https://prove2.me/theorems/17a8fc78-da8e-4cdf-b1e7-1623afbe04c3
-- title:
--   isItoVersion trig
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.isItoVersion_trig` is extracted from `LevyStochCalc.Brownian.CellCharacter`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_CellCharacter_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The trigonometric functions of a Brownian increment are Itô processes

For a continuous version `X` of `∫ 1_{(a,b]} dW`, Itô's formula for the scaled cosine and sine
says that `cos (l X)` and `sin (l X)` are themselves Itô processes: their integrands are
`∓ l sin (l X) 1_{(a,b]}` and `± l cos (l X) 1_{(a,b]}` and their drifts are
`−(l²/2) cos (l X) 1_{(a,b]}²` and `−(l²/2) sin (l X) 1_{(a,b]}²`, with initial value `1` and `0`.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

section Version

variable {P : Measure Ω} [IsProbabilityMeasure P] {W : LevyStochCalc.Brownian.BrownianMotion P}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {hℱ : IsBrownianFiltration W ℱ}
  {a b : ℝ}
  {hm : Measurable (Function.uncurry (indIoc Ω a b))}
  {hp : Probability.ProgressivelyMeasurable ℱ (indIoc Ω a b)}
  {hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X : ℝ → Ω → ℝ}

theorem _root_.LevyStochCalc.Brownian.Ito.isItoVersion_trig
    (hX : IsItoVersion W ℱ hℱ (indIoc Ω a b) hm hp hq (fun _ => 0) (fun _ _ => 0) X)
    (l : ℝ) {g g' : ℝ → ℝ} (hgc : Continuous g)
    (hmg : Measurable (Function.uncurry fun ω s => g' (X s ω) * indIoc Ω a b ω s))
    (hpg : Probability.ProgressivelyMeasurable ℱ fun ω s => g' (X s ω) * indIoc Ω a b ω s)
    (hqg : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖g' (X s ω) * indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hito : ∀ T : ℝ, 0 < T →
      (fun ω : Ω => g (l * X T ω) - g (l * X 0 ω)) =ᵐ[P] fun ω =>
        stochasticIntegralBrownian W ℱ hℱ
            (fun ω s => g' (X s ω) * indIoc Ω a b ω s) hmg hpg hqg T ω
          + 1 / 2 * ∫ s in Set.Ioc (0 : ℝ) T,
              (-l ^ 2 * g (l * X s ω)) * indIoc Ω a b ω s ^ 2 ∂volume)
    (hX0 : X 0 =ᵐ[P] fun _ => (0 : ℝ)) :
    IsItoVersion W ℱ hℱ (fun ω s => g' (X s ω) * indIoc Ω a b ω s) hmg hpg hqg
      (fun _ => g 0) (trigDriftCell l (fun x => g (l * x)) X a b)
      (fun t ω => g (l * X t ω)) := by sorry
