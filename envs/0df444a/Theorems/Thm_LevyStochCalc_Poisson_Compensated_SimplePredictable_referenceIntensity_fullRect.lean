-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_Compensated_SimplePredictable_referenceIntensity_fullRect
-- name    : LevyStochCalc.Poisson.Compensated.SimplePredictable.referenceIntensity_fullRect
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T00:23:51.501201+00:00
-- url     : https://prove2.me/theorems/fa1745f1-bef7-4d01-b991-f8de64183866
-- title:
--   referenceIntensity fullRect
-- statement:
--   The source theorem `LevyStochCalc.Poisson.Compensated.SimplePredictable.referenceIntensity_fullRect` is extracted from `LevyStochCalc.Poisson.CompensatedSimple`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedSimple_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Compensated Poisson integral: simple predictable integrands

The simple predictable integrands `φ = ∑_i ξ_i · 1_{(t_i, t_{i+1}] × A_i}` and
their integral `simpleIntegral` against the compensated Poisson measure
`Ñ(dt, de) := N(dt, de) − ν(de) dt`, with the indicator/rectangle bookkeeping
lemmas. The moment identities are in `Poisson/CompensatedMoments.lean`; the
L²-isometry in `Poisson/CompensatedIsometry.lean`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

theorem _root_.LevyStochCalc.Poisson.Compensated.SimplePredictable.referenceIntensity_fullRect
    {ν : Measure E} [SigmaFinite ν] {T : ℝ}
    (φ : SimplePredictable Ω E ν T) (i : Fin φ.N) :
    LevyStochCalc.Poisson.referenceIntensity ν (φ.fullRect i)
      = ENNReal.ofReal (φ.partition i.succ - φ.partition i.castSucc) * ν (φ.A i) := by sorry
