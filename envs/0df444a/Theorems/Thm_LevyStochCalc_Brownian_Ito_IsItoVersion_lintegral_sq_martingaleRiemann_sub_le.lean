-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_IsItoVersion_lintegral_sq_martingaleRiemann_sub_le
-- name    : LevyStochCalc.Brownian.Ito.IsItoVersion.lintegral_sq_martingaleRiemann_sub_le
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:35:56.693856+00:00
-- url     : https://prove2.me/theorems/f6bbdc9b-ce67-4f26-a9f0-872588904701
-- title:
--   lintegral sq martingaleRiemann sub le
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.IsItoVersion.lintegral_sq_martingaleRiemann_sub_le` is extracted from `LevyStochCalc.Brownian.ItoMartingaleRiemann`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoFormula_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoGridPartition_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoProcessVersion_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The martingale Riemann sum of the Itô formula

Freezing a Lipschitz function of a continuous Itô process at the left endpoints of a uniform
grid and pairing it with the Itô integral's increments gives a Riemann sum for
`∫_0^T φ(X_s)·H_s dW_s`, with an `L²` error of order `√(T/m)`.

## Main statements

* `LevyStochCalc.Brownian.Ito.lintegral_sq_bounded_mul_lt_top` — a bounded weight preserves the
  `L²` bound on an integrand.
* `LevyStochCalc.Brownian.Ito.IsItoVersion.lintegral_sq_frozen_sub_le` — the `L²` distance
  between the frozen step weight and the weight itself.
* `LevyStochCalc.Brownian.Ito.IsItoVersion.lintegral_sq_martingaleRiemann_sub_le` — the `L²`
  error of the martingale Riemann sum.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

section Weight

variable {P : Measure Ω} [IsProbabilityMeasure P] {H : Ω → ℝ → ℝ}

end Weight

section Frozen

variable {P : Measure Ω} [IsProbabilityMeasure P] {W : LevyStochCalc.Brownian.BrownianMotion P}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {hℱ : IsBrownianFiltration W ℱ}
  {H : Ω → ℝ → ℝ} {hm : Measurable (Function.uncurry H)}
  {hp : Probability.ProgressivelyMeasurable ℱ H}
  {hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X₀ : Ω → ℝ} {bdrift : Ω → ℝ → ℝ} {X : ℝ → Ω → ℝ}
  {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)

include hC0 hCH in

theorem _root_.LevyStochCalc.Brownian.Ito.IsItoVersion.lintegral_sq_martingaleRiemann_sub_le
    (h : IsItoVersion W ℱ hℱ H hm hp hq X₀ bdrift X)
    (hbm : Measurable (Function.uncurry bdrift))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (ω : Ω) (s : ℝ), |bdrift ω s| ≤ B)
    {φ : ℝ → ℝ} {Kφ : ℝ} (hφbd : ∀ x, |φ x| ≤ Kφ)
    {L : ℝ} (hL0 : 0 ≤ L) (hφlip : ∀ x y : ℝ, |φ x - φ y| ≤ L * |x - y|)
    (hmg : Measurable (Function.uncurry fun ω s => φ (X s ω) * H ω s))
    (hpg : Probability.ProgressivelyMeasurable ℱ fun ω s => φ (X s ω) * H ω s)
    (hqg : ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖φ (X s ω) * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    ∫⁻ ω, (‖(∑ i : Fin m, φ (X (unifGrid T m (i : ℕ)) ω)
          * (stochasticIntegralBrownian W ℱ hℱ H hm hp hq
              (unifGrid T m ((i : ℕ) + 1)) ω
            - stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m (i : ℕ)) ω))
        - stochasticIntegralBrownian W ℱ hℱ (fun ω s => φ (X s ω) * H ω s)
            hmg hpg hqg T ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ ENNReal.ofReal (C ^ 2) * (ENNReal.ofReal (L ^ 2)
        * ENNReal.ofReal (T * (2 * (B * (T / (m : ℝ))) ^ 2
          + 2 * (C ^ 2 * (T / (m : ℝ)))))) := by sorry
