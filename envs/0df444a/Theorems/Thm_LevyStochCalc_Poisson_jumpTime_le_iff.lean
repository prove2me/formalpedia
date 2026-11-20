-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_jumpTime_le_iff
-- name    : LevyStochCalc.Poisson.jumpTime_le_iff
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T15:29:27.081202+00:00
-- url     : https://prove2.me/theorems/a0630c79-c871-4fed-aa2c-1aba1b06facb
-- title:
--   jumpTime le iff
-- statement:
--   The source theorem `LevyStochCalc.Poisson.jumpTime_le_iff` is extracted from `LevyStochCalc.Poisson.JumpTimes`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_JumpTimes_F001

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

theorem _root_.LevyStochCalc.Poisson.jumpTime_le_iff (hA : MeasurableSet A) {i : ℕ} {t : ℝ} (ht : 0 ≤ t) {ω : Ω}
    (hfin : arrivalCount N A (t + 1) ω ≠ ⊤) :
    jumpTime N A i ω ≤ (t : WithTop ℝ) ↔ (i : ℝ≥0∞) ≤ arrivalCount N A t ω := by sorry
