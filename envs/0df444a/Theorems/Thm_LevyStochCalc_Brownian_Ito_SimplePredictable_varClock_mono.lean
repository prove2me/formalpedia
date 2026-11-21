-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_SimplePredictable_varClock_mono
-- name    : LevyStochCalc.Brownian.Ito.SimplePredictable.varClock_mono
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T18:51:23.91254+00:00
-- url     : https://prove2.me/theorems/ede44de6-7f72-497f-b439-03c86db80a6d
-- title:
--   varClock mono
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.SimplePredictable.varClock_mono` is extracted from `LevyStochCalc.Brownian.ItoFourthMomentIncrements`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoFourthMomentIncrements_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Moments of a Brownian increment and the partial sums of the elementary integral

The moments of a centred real Gaussian and of a Brownian increment: they scale with the standard
deviation, the odd ones vanish, and a random variable measurable before the increment factors out
of the integral against any power of it. On top of this the elementary integral of a simple
integrand is presented as the partial sums `SimplePredictable.partialSum` of its summands, with
their measurability, adaptedness and `Lᵖ` membership, and the variance budget
`SimplePredictable.varClock c k = ∑_{j < k} c_j² (τ_{j+1} − τ_j)` of a per-tile coefficient
bound `c`.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

section Increments

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)

end Increments

namespace SimplePredictable

variable {T : ℝ} (G : SimplePredictable Ω T)
  {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)

theorem _root_.LevyStochCalc.Brownian.Ito.SimplePredictable.varClock_mono (c : Fin G.N → ℝ) {k l : ℕ} (h : k ≤ l) :
    G.varClock c k ≤ G.varClock c l := by sorry
