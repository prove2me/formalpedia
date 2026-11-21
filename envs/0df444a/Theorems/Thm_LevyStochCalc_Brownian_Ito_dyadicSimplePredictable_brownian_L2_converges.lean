-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_dyadicSimplePredictable_brownian_L2_converges
-- name    : LevyStochCalc.Brownian.Ito.dyadicSimplePredictable_brownian_L2_converges
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T12:20:59.672887+00:00
-- url     : https://prove2.me/theorems/0b3a5309-76cb-4e47-a2a3-877f4738d37b
-- title:
--   dyadicSimplePredictable brownian L2 converges
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.dyadicSimplePredictable_brownian_L2_converges` is extracted from `LevyStochCalc.Brownian.ItoDensityPointwise`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoDensityPointwise_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Almost-everywhere convergence of the dyadic averages

Lebesgue differentiation for a bounded jointly measurable integrand: the dyadic cell
averages, shifted and unshifted, converge to the integrand at almost every point of
`Ω × [0,T]`, and for the unshifted family the convergence also holds in `L²`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
-- `open Classical` is avoided at file scope; explicit decidability is used.

namespace LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

theorem _root_.LevyStochCalc.Brownian.Ito.dyadicSimplePredictable_brownian_L2_converges
    {P : Measure Ω} [IsProbabilityMeasure P]
    {T : ℝ} (hT : 0 < T)
    (g : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M) :
    Filter.Tendsto
      (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖g ω s - (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval s ω‖₊
          : ℝ≥0∞) ^ 2 ∂volume ∂P)
      Filter.atTop (nhds 0) := by sorry
