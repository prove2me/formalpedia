-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_isStoppingTime_jumpTime_of_complete
-- name    : LevyStochCalc.Poisson.isStoppingTime_jumpTime_of_complete
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T15:32:09.093711+00:00
-- url     : https://prove2.me/theorems/5f946133-04ac-475e-ae5a-6c8765580776
-- title:
--   isStoppingTime jumpTime of complete
-- statement:
--   The source theorem `LevyStochCalc.Poisson.isStoppingTime_jumpTime_of_complete` is extracted from `LevyStochCalc.Poisson.JumpTimesComplete`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_JumpTimes_F001
import Definitions.Def_LevyStochCalc_Poisson_JumpTimes_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Arrival times as stopping times for a filtration containing the null sets

For a filtration whose time-zero σ-algebra contains the `P`-null sets, the arrival times
`jumpTime N A i` of a Poisson random measure `N` in a mark set `A` of finite intensity are
stopping times for the filtration itself: the counting process is almost surely finite at every
time, and the exceptional set is absorbed by the null sets of the time-zero σ-algebra. This
avoids both the pathwise finiteness hypothesis of `isStoppingTime_jumpTime` and the passage to
the right-continuous filtration in `isStoppingTime_jumpTime_rightCont`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

variable (N : PoissonRandomMeasure P ν) (A : Set E)

theorem _root_.LevyStochCalc.Poisson.isStoppingTime_jumpTime_of_complete {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hℱ : IsPoissonFiltration N ℱ) (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (i : ℕ) :
    IsStoppingTime ℱ (jumpTime N A i) := by sorry
