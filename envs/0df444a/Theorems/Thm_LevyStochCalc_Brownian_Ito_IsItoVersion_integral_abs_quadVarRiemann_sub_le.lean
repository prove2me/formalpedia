-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_IsItoVersion_integral_abs_quadVarRiemann_sub_le
-- name    : LevyStochCalc.Brownian.Ito.IsItoVersion.integral_abs_quadVarRiemann_sub_le
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:38:33.917015+00:00
-- url     : https://prove2.me/theorems/5f48d51e-82df-490f-acdc-e062864a70d7
-- title:
--   integral abs quadVarRiemann sub le
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.IsItoVersion.integral_abs_quadVarRiemann_sub_le` is extracted from `LevyStochCalc.Brownian.ItoQuadVarRiemann`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoQuadVarRiemann_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The quadratic-variation Riemann sum of the Itô formula

Squaring the increments of a continuous Itô process across a uniform grid and weighting them by
a bounded Lipschitz function of the process gives a Riemann sum for `∫_0^T φ(X_s)·H_s² ds`. The
drift square and the cross term are `O(1/m)` and `O(m^{-1/2})`, the compensated squares are
`O(m^{-1/2})` by the martingale-difference bound, and the compensator itself is a frozen-weight
Riemann sum for the density `H²`.

## Main statements

* `LevyStochCalc.Brownian.Ito.IsItoVersion.integral_abs_sum_drift_sq_le` — the drift-square sum.
* `LevyStochCalc.Brownian.Ito.IsItoVersion.integral_abs_sum_cross_le` — the cross term.
* `LevyStochCalc.Brownian.Ito.IsItoVersion.integral_abs_sum_quadVar_le` — the compensated
  squares.
* `LevyStochCalc.Brownian.Ito.IsItoVersion.integral_abs_quadVarRiemann_sub_le` — the four
  pieces together.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

section QuadVarRiemann

variable {P : Measure Ω} [IsProbabilityMeasure P] {W : LevyStochCalc.Brownian.BrownianMotion P}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {hℱ : IsBrownianFiltration W ℱ}
  {H : Ω → ℝ → ℝ} {hm : Measurable (Function.uncurry H)}
  {hp : Probability.ProgressivelyMeasurable ℱ H}
  {hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X₀ : Ω → ℝ} {bdrift : Ω → ℝ → ℝ} {X : ℝ → Ω → ℝ}
  {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)

include hC0 hCH in

theorem _root_.LevyStochCalc.Brownian.Ito.IsItoVersion.integral_abs_quadVarRiemann_sub_le
    (h : IsItoVersion W ℱ hℱ H hm hp hq X₀ bdrift X)
    (hbm : Measurable (Function.uncurry bdrift))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (ω : Ω) (s : ℝ), |bdrift ω s| ≤ B)
    {φ : ℝ → ℝ} (hφc : Continuous φ) {Kφ : ℝ} (hKφ0 : 0 ≤ Kφ) (hφbd : ∀ x, |φ x| ≤ Kφ)
    {L : ℝ} (hL0 : 0 ≤ L) (hφlip : ∀ x y : ℝ, |φ x - φ y| ≤ L * |x - y|)
    {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    MeasureTheory.Integrable (fun ω : Ω => (∑ i ∈ Finset.range m,
          φ (X (unifGrid T m i) ω)
            * (X (unifGrid T m (i + 1)) ω - X (unifGrid T m i) ω) ^ 2)
        - ∫ s in Set.Ioc (0 : ℝ) T, φ (X s ω) * H ω s ^ 2 ∂volume) P
      ∧ ∫ ω, |(∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
            * (X (unifGrid T m (i + 1)) ω - X (unifGrid T m i) ω) ^ 2)
          - ∫ s in Set.Ioc (0 : ℝ) T, φ (X s ω) * H ω s ^ 2 ∂volume| ∂P
        ≤ (m : ℝ) * (Kφ * (B * (T / (m : ℝ))) ^ 2)
        + (m : ℝ) * (2 * Kφ * (B * (T / (m : ℝ))) * (C * Real.sqrt (T / (m : ℝ))))
        + Real.sqrt (Kφ ^ 2 * ((2 * (6 + gaussianFourthMoment) + 2) * C ^ 4)
            * ((m : ℝ) * (T / (m : ℝ)) ^ 2))
        + L * C ^ 2 * (T * (B * (T / (m : ℝ)) + C * Real.sqrt (T / (m : ℝ)))) := by sorry
