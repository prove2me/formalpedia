-- Prove2me | Theorems.Thm_LevyStochCalc_BSDEJ_Contraction_two_mul_mul_generator_sub_le
-- name    : LevyStochCalc.BSDEJ.Contraction.two_mul_mul_generator_sub_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T19:24:35.494446+00:00
-- url     : https://prove2.me/theorems/be481b1a-1c57-4a5a-bfb0-e97292d7b127
-- title:
--   two mul mul generator sub le
-- statement:
--   The source theorem `LevyStochCalc.BSDEJ.Contraction.two_mul_mul_generator_sub_le` is extracted from `LevyStochCalc.BSDEJ.YoungLipschitz`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_Existence_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Young and Lipschitz pointwise rate bounds for a BSDEJ generator

Pure real-variable inequalities behind the BSDEJ contraction estimate: a weighted Young
inequality (`two_mul_mul_le_young`), a three-term square bound (`sq_add_add_le_three`), a bound
of the `Fin d → ℝ` sup norm by the sum of squared coordinates (`sq_norm_pi_le_sum_sq`), their
combination into a pointwise bound on the squared increment of a Lipschitz generator
(`sq_generator_sub_le`) and on `2 * (a * Δf)` for that increment (`two_mul_mul_generator_sub_le`
and its negated-argument form `two_mul_mul_generator_sub_le'`), and the contraction threshold on
the Young weight `β = max 2 (24 * L ^ 2)` (`contraction_factor_le`).
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.Contraction

variable {d : ℕ} {E : Type*} [MeasurableSpace E] {ν : Measure E}
variable {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ} {L : ℝ}

theorem _root_.LevyStochCalc.BSDEJ.Contraction.two_mul_mul_generator_sub_le {β : ℝ} (hβ : 0 < β) (hL : 0 ≤ L)
    (hlip : ∀ (s y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ),
      (‖f s y₁ z₁ u₁ - f s y₂ z₂ u₂‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal L *
        ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)))
    (s y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ)
    (hu : ∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν ≠ ⊤) (a : ℝ) :
    2 * (a * (f s y₁ z₁ u₁ - f s y₂ z₂ u₂))
      ≤ β / 2 * a ^ 2 + 6 * L ^ 2 / β * ((y₁ - y₂) ^ 2 + (∑ j, (z₁ j - z₂ j) ^ 2)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν).toReal) := by sorry
