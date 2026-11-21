-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_SimplePredictable_varClock_le_Ioc
-- name    : LevyStochCalc.Brownian.Ito.SimplePredictable.varClock_le_Ioc
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:09:43.855202+00:00
-- url     : https://prove2.me/theorems/07711ae3-fcce-4ce8-8401-85c4e6b30f6d
-- title:
--   varClock le Ioc
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.SimplePredictable.varClock_le_Ioc` is extracted from `LevyStochCalc.Brownian.ItoIncrementMomentRestrict`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoIncrementMomentRestrict_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Restriction of a simple predictable integrand to `(a, b]`

An adapted simple integrand `G` multiplied by the simple integrand `1_{(a, b]}` on their common
refinement is again an adapted simple integrand: its evaluation is `1_{(a, b]}·G`, its
coefficients vanish on every tile not contained in `(a, b]` and stay bounded by any bound on the
coefficients of `G`, and the variance budget of that per-tile bound is at most `C²(b − a)`.

## Main statements

* `SimplePredictable.eval_of_mem_Ioc` — a simple integrand evaluates to a tile's coefficient
  at every time in that tile.
* `SimplePredictable.varClock_le_Ioc` — the variance budget of the per-tile bound
  `C·1_{tile ⊆ (a, b]}` is at most `C²(b − a)`.
* `SimplePredictable.exists_restrict_Ioc` — an adapted simple integrand multiplied by
  `1_{(a, b]}` on their common refinement, with coefficients vanishing off `(a, b]`.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

theorem _root_.LevyStochCalc.Brownian.Ito.SimplePredictable.varClock_le_Ioc {T : ℝ} (H : SimplePredictable Ω T) {a b C : ℝ}
    (hab : a ≤ b) :
    H.varClock (fun j => if a ≤ H.partition j.castSucc ∧ H.partition j.succ ≤ b then C else 0)
        H.N ≤ C ^ 2 * (b - a) := by sorry
