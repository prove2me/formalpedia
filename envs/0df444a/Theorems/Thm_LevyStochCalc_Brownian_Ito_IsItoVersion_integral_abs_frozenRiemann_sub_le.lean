-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_IsItoVersion_integral_abs_frozenRiemann_sub_le
-- name    : LevyStochCalc.Brownian.Ito.IsItoVersion.integral_abs_frozenRiemann_sub_le
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:35:13.490536+00:00
-- url     : https://prove2.me/theorems/f60c82db-8372-4c88-95b1-3a3a2c57e1ce
-- title:
--   integral abs frozenRiemann sub le
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.IsItoVersion.integral_abs_frozenRiemann_sub_le` is extracted from `LevyStochCalc.Brownian.ItoTimeRiemann`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoProcessVersion_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoTimeRiemann_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Frozen-weight Riemann sums of the Itô formula

Freezing a Lipschitz function of a continuous Itô process at the left endpoints of a uniform
grid and pairing it with the cell integrals of a bounded time density gives a Riemann sum for
`∫_0^T φ(X_s)·w_s ds`, with an `L¹` error of order `√(T/m)`. Both the process's own drift and
the squared diffusion coefficient are admissible densities.

## Main statements

* `LevyStochCalc.Brownian.Ito.sum_setIntegral_unifGrid` — the cells of the uniform grid
  partition the time integral.
* `LevyStochCalc.Brownian.Ito.IsItoVersion.integral_abs_frozenRiemann_sub_le` — the `L¹` error
  of a frozen-weight Riemann sum.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

section Riemann

variable {P : Measure Ω} [IsProbabilityMeasure P] {W : LevyStochCalc.Brownian.BrownianMotion P}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {hℱ : IsBrownianFiltration W ℱ}
  {H : Ω → ℝ → ℝ} {hm : Measurable (Function.uncurry H)}
  {hp : Probability.ProgressivelyMeasurable ℱ H}
  {hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X₀ : Ω → ℝ} {bdrift : Ω → ℝ → ℝ} {X : ℝ → Ω → ℝ}
  {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)

include hC0 hCH in

theorem _root_.LevyStochCalc.Brownian.Ito.IsItoVersion.integral_abs_frozenRiemann_sub_le
    (h : IsItoVersion W ℱ hℱ H hm hp hq X₀ bdrift X)
    (hbm : Measurable (Function.uncurry bdrift))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (ω : Ω) (s : ℝ), |bdrift ω s| ≤ B)
    (wgt : Ω → ℝ → ℝ) (hwm : Measurable (Function.uncurry wgt))
    {A : ℝ} (hA0 : 0 ≤ A) (hA : ∀ (ω : Ω) (s : ℝ), |wgt ω s| ≤ A)
    {φ : ℝ → ℝ} (hφc : Continuous φ) {Kφ : ℝ} (hφbd : ∀ x, |φ x| ≤ Kφ)
    {L : ℝ} (hL0 : 0 ≤ L) (hφlip : ∀ x y : ℝ, |φ x - φ y| ≤ L * |x - y|)
    {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    MeasureTheory.Integrable (fun ω : Ω =>
        (∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
            * ∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), wgt ω s ∂volume)
          - ∫ s in Set.Ioc (0 : ℝ) T, φ (X s ω) * wgt ω s ∂volume) P
      ∧ ∫ ω, |(∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
            * ∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), wgt ω s ∂volume)
          - ∫ s in Set.Ioc (0 : ℝ) T, φ (X s ω) * wgt ω s ∂volume| ∂P
        ≤ L * A * (T * (B * (T / (m : ℝ)) + C * Real.sqrt (T / (m : ℝ)))) := by sorry
