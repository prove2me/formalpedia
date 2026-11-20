-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_exists_strictMono_enum_jumpTime
-- name    : LevyStochCalc.Poisson.exists_strictMono_enum_jumpTime
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T15:31:14.143725+00:00
-- url     : https://prove2.me/theorems/67a84cdd-3e64-41bb-829e-9ab688a1d8ae
-- title:
--   exists strictMono enum jumpTime
-- statement:
--   The source theorem `LevyStochCalc.Poisson.exists_strictMono_enum_jumpTime` is extracted from `LevyStochCalc.Poisson.JumpTimes`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_JumpTimes_F002

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

end JumpTime

section Finiteness

variable (N : PoissonRandomMeasure P ν) (A : Set E)

theorem _root_.LevyStochCalc.Poisson.exists_strictMono_enum_jumpTime (hA : MeasurableSet A) {T : ℝ} (hT : 0 ≤ T) {ω : Ω}
    (hfin : arrivalCount N A (T + 1) ω ≠ ⊤) :
    ∃ (k : ℕ) (e : Fin k → ℝ), StrictMono e ∧
      Set.range e = {s : ℝ | ∃ i : ℕ, jumpTime N A i ω = (s : WithTop ℝ) ∧ s ≤ T} := by sorry
