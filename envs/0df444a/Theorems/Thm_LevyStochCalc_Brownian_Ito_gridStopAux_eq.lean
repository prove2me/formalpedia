-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_gridStopAux_eq
-- name    : LevyStochCalc.Brownian.Ito.gridStopAux_eq
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:06:41.722175+00:00
-- url     : https://prove2.me/theorems/6176b57e-88bc-4d5d-a747-ec1f38160ddf
-- title:
--   gridStopAux eq
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.gridStopAux_eq` is extracted from `LevyStochCalc.Brownian.ItoLocality`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoLocality_F000

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
theorem _root_.LevyStochCalc.Brownian.Ito.gridStopAux_eq (t : ℝ) (n k : ℕ) (ω : Ω) :
    (∃ j ≤ k, gridStopAux τ t n k ω = ((gridPt t n j : ℝ) : WithTop ℝ))
      ∨ gridStopAux τ t n k ω = ⊤ := by sorry
