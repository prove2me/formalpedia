-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_truncation_L2_converges_brownian
-- name    : LevyStochCalc.Brownian.Ito.truncation_L2_converges_brownian
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T08:03:38.313191+00:00
-- url     : https://prove2.me/theorems/6974ad15-6dee-4d96-afb4-aae848baf992
-- title:
--   truncation L2 converges brownian
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.truncation_L2_converges_brownian` is extracted from `LevyStochCalc.Brownian.ItoDensityDyadicAverages`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoDensityDyadicAverages_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Truncation in `L²` and dyadic cell averages

Truncation of an `L²(Ω × [0,T])` integrand at level `M` together with the `L²` error it
incurs, the dyadic partition of `[0,T]`, the cell averages of an integrand over the
partition intervals, and the simple predictable process whose values on the `n`-th dyadic
grid are those averages.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
-- `open Classical` is avoided at file scope; explicit decidability is used.

namespace LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

set_option maxHeartbeats 800000 in
-- maxHeartbeats: typechecker budget for proof-heavy goal below.

theorem _root_.LevyStochCalc.Brownian.Ito.truncation_L2_converges_brownian
    {P : Measure Ω} [IsProbabilityMeasure P]
    {T : ℝ}
    (H : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry H))
    (h_sq_int : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    Filter.Tendsto
      (fun M : ℕ => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s - max (-(M : ℝ)) (min (M : ℝ) (H ω s))‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P)
      Filter.atTop (nhds 0) := by sorry
