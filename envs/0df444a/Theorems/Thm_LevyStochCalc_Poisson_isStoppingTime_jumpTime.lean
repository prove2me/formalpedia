-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_isStoppingTime_jumpTime
-- name    : LevyStochCalc.Poisson.isStoppingTime_jumpTime
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T12:51:49.301925+00:00
-- url     : https://prove2.me/theorems/faab2d58-6166-4657-9002-a372a5534fb1
-- title:
--   isStoppingTime jumpTime
-- statement:
--   The source theorem `LevyStochCalc.Poisson.isStoppingTime_jumpTime` is extracted from `LevyStochCalc.Poisson.JumpTimes`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_JumpTimes_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Arrival times of a Poisson random measure on a mark set

`arrivalCount N A t ω` is the number of points of a Poisson random measure `N` whose time lies in
`(0, t]` and whose mark lies in `A`. It is monotone in the time, measurable for every filtration
for which `N` is a Poisson random measure, and right-continuous at every time from which it stays
finite. The `i`-th arrival time `jumpTime N A i` is the first nonnegative time at which the count
reaches `i`, and `⊤` when the count never reaches `i`; it is a stopping time for the
right-continuous filtration `ℱ₊`, and for `ℱ` itself when the counting process is everywhere
finite. Over a window on which the count is finite only finitely many arrival times occur, and
they carry a strictly monotone enumeration.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

section MarkCount

variable (N : PoissonRandomMeasure P ν) (A : Set E)

end MarkCount

section JumpTime

variable (N : PoissonRandomMeasure P ν) (A : Set E)

theorem _root_.LevyStochCalc.Poisson.isStoppingTime_jumpTime {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hℱ : IsPoissonFiltration N ℱ) (hA : MeasurableSet A)
    (hfin : ∀ (ω : Ω) (t : ℝ), arrivalCount N A t ω ≠ ⊤) (i : ℕ) :
    IsStoppingTime ℱ (jumpTime N A i) := by sorry
