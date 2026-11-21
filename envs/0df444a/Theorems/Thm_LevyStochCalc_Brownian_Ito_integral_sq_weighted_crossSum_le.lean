-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_integral_sq_weighted_crossSum_le
-- name    : LevyStochCalc.Brownian.Ito.integral_sq_weighted_crossSum_le
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:36:02.373225+00:00
-- url     : https://prove2.me/theorems/eb2a9f32-7ad7-47d8-b447-ebf2d0b30bb8
-- title:
--   integral sq weighted crossSum le
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.integral_sq_weighted_crossSum_le` is extracted from `LevyStochCalc.Brownian.CrossVariationSum`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_CrossVariationSum_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Weighted sums of cross increments

For two distinct Brownian coordinates the product of the increments of the Itô integrals across a
cell is conditionally centred at the cell's left endpoint, so a weighted sum of such products over
a partition is a sum of martingale differences whenever the weights are measurable at the left
endpoints. Its second moment is therefore the sum of the termwise second moments, and each of
those is bounded through the fourth moments of the two increments.

## Main statements

* `LevyStochCalc.Brownian.Ito.integrable_sq_mul_and_le` — the square of a product is integrable
  with second moment at most half the sum of the fourth moments.
* `LevyStochCalc.Brownian.Ito.crossIncrement` — the product of the increments of the Itô
  integrals against two coordinates across a cell.
* `LevyStochCalc.Brownian.Ito.integrable_sq_crossIncrement_and_le` — its square is integrable,
  with second moment at most `(6 + c)·(C_H⁴ + C_K⁴)/2·(b − a)²`.
* `LevyStochCalc.Brownian.Ito.integral_sq_weighted_crossSum_le` — the second moment of a weighted
  sum over a grid is at most `D²·(6 + c)·(C_H⁴ + C_K⁴)/2·∑ᵢ (tᵢ₊₁ − tᵢ)²`.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section CrossSum

open LevyStochCalc.Brownian.Multidim

variable {d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)
  {H K : Ω → ℝ → ℝ} (hHm : Measurable (Function.uncurry H))
  (hHp : Probability.ProgressivelyMeasurable ℱ H)
  (hHs : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  (hKm : Measurable (Function.uncurry K))
  (hKp : Probability.ProgressivelyMeasurable ℱ K)
  (hKs : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

variable {CH CK : ℝ} (hCH0 : 0 ≤ CH) (hCH : ∀ ω s, |H ω s| ≤ CH)
  (hCK0 : 0 ≤ CK) (hCK : ∀ ω s, |K ω s| ≤ CK)

include hCH0 hCH hCK0 hCK in

theorem _root_.LevyStochCalc.Brownian.Ito.integral_sq_weighted_crossSum_le {i j : Fin d} (hij : i ≠ j)
    (t : ℕ → ℝ) (h0 : 0 ≤ t 0) (ht : ∀ k, t k < t (k + 1))
    (g : ℕ → Ω → ℝ) (hg : ∀ k, StronglyMeasurable[ℱ (t k)] (g k))
    {D : ℝ} (hD0 : 0 ≤ D) (hgD : ∀ (k : ℕ) (ω : Ω), |g k ω| ≤ D) (n : ℕ) :
    ∫ ω, (∑ k ∈ Finset.range n, g k ω *
        crossIncrement W hcoord hHm hHp hHs hKm hKp hKs i j (t k) (t (k + 1)) ω) ^ 2 ∂P
      ≤ D ^ 2 * ((6 + gaussianFourthMoment) * (CH ^ 4 + CK ^ 4) / 2)
        * ∑ k ∈ Finset.range n, (t (k + 1) - t k) ^ 2 := by sorry
