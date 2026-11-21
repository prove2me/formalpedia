-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_abs_trigDriftCell_le
-- name    : LevyStochCalc.Brownian.Ito.abs_trigDriftCell_le
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:53:53.695656+00:00
-- url     : https://prove2.me/theorems/de9a6434-d7c5-4432-954c-dc13cb6b2b02
-- title:
--   abs trigDriftCell le
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.abs_trigDriftCell_le` is extracted from `LevyStochCalc.Brownian.CellCharacter`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_CellCharacter_F000

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

theorem _root_.LevyStochCalc.Brownian.Ito.abs_trigDriftCell_le (l : ℝ) {g : ℝ → ℝ} {M : ℝ} (hg : ∀ x, |g x| ≤ M) (hM0 : 0 ≤ M)
    (X : ℝ → Ω → ℝ) (a b : ℝ) (ω : Ω) (s : ℝ) :
    |trigDriftCell l g X a b ω s| ≤ 1 / 2 * (l ^ 2 * M) := by sorry
