-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_condExp_quadVarIncrement
-- name    : LevyStochCalc.Brownian.Ito.condExp_quadVarIncrement
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:18:45.561497+00:00
-- url     : https://prove2.me/theorems/d17bdf21-8500-4283-8162-86553b6f2b7e
-- title:
--   condExp quadVarIncrement
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.condExp_quadVarIncrement` is extracted from `LevyStochCalc.Brownian.ItoQuadVarSum`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionQuadVar_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionQuadVar_F002
import Definitions.Def_LevyStochCalc_Brownian_ItoQuadVarSum_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Compensated square increments of the Itô integral

The increment `(M_b − M_a)² − ∫_a^b H_s² ds` of the compensated square of the Itô integral is
conditionally centred at its left endpoint, so a weighted sum of such increments over a
partition is a sum of martingale differences.

## Main statements

* `LevyStochCalc.Brownian.Ito.quadVarIncrement` — the compensated square increment.
* `LevyStochCalc.Brownian.Ito.condExp_quadVarIncrement` — it is conditionally centred at the
  left endpoint.
* `LevyStochCalc.Brownian.Ito.compensator_sub_bounds` — the compensator increment across
  `(a, b]` lies between `0` and `C²(b − a)`.
* `LevyStochCalc.Brownian.Ito.integral_sq_quadVarIncrement_le` — its second moment is at most
  `(2(6 + c) + 2)·C⁴·(b − a)²`.
* `LevyStochCalc.Brownian.Ito.integral_sq_weighted_quadVarSum_le` — the second moment of a
  weighted sum over a grid is at most `D²·(2(6 + c) + 2)·C⁴·∑ᵢ (tᵢ₊₁ − tᵢ)²`.
* `LevyStochCalc.Brownian.Ito.exists_continuous_modification_stochasticIntegralBrownian` — the
  Itô integral of a bounded integrand has a modification with continuous paths.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

section QuadVarIncrement

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

include hℱ in

theorem _root_.LevyStochCalc.Brownian.Ito.condExp_quadVarIncrement {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    P[quadVarIncrement W ℱ hℱ H hm hp hq a b | ℱ.rightCont a] =ᵐ[P] 0 := by sorry
