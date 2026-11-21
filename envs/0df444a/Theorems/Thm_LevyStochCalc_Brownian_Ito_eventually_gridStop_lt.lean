-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_eventually_gridStop_lt
-- name    : LevyStochCalc.Brownian.Ito.eventually_gridStop_lt
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T19:10:45.245173+00:00
-- url     : https://prove2.me/theorems/267f9964-c7ed-438c-be93-7b9df68cdca4
-- title:
--   eventually gridStop lt
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.eventually_gridStop_lt` is extracted from `LevyStochCalc.Brownian.ItoLocality`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoLocality_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The local property of the Itô integral

Cutting the integrand off at a stopping time `τ` does not change the integral at a time the
stopping time has not yet reached. The stopping time is approximated from above by the
finite-range stopping times that stop at the first point of a uniform grid strictly beyond it,
for which the finite-range optional stopping identity applies directly; the approximation
converges in energy, and an `L²` squeeze removes the approximation.

## Main statements

* `LevyStochCalc.Brownian.Ito.stepStop`, `gridStop` — the two-valued and the grid stopping times.
* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stopped_eq_of_le` — the local property.
* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_of_pos` — the integral to a
  positive time sees the integrand only at positive times.
* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_of_le` — two integrands agreeing
  up to a stopping time have the same integral where that time has not been reached.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (τ : Ω → WithTop ℝ)

section GridStop

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in

theorem _root_.LevyStochCalc.Brownian.Ito.eventually_gridStop_lt {t : ℝ} (ht : 0 < t) (ω : Ω) {s : ℝ} (hs : 0 < s) (hst : s ≤ t)
    (hτs : τ ω < ((s : ℝ) : WithTop ℝ)) :
    ∀ᶠ n in Filter.atTop, gridStop τ t n ω < ((s : ℝ) : WithTop ℝ) := by sorry
