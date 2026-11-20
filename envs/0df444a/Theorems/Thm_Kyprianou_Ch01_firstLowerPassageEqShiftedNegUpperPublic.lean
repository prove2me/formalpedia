-- Prove2me | Theorems.Thm_Kyprianou_Ch01_firstLowerPassageEqShiftedNegUpperPublic
-- name    : Kyprianou.Ch01.firstLowerPassageEqShiftedNegUpperPublic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T07:41:59.746301+00:00
-- url     : https://prove2.me/theorems/a8bb10fe-11c8-44a6-a438-8dbf31b42ce3
-- title:
--   First strict lower passage with nonzero initial capital equals a shifted negated first upper passage
-- statement:
--   For every real sample path, initial capital x, and barrier b, the strict first downcrossing time of x+X below b equals the first strict upcrossing time of the negated path -X above x-b. Both times use the original positive-time strict crossing and infinity convention. Prove pointwise by elementary rearrangement of the threshold inequality and equality of the crossing-time sets.
-- source:
--   Kyprianou (2006), Chapter 1 McKean perpetual put, identifying downcrossing with upcrossing under reflection.

import Mathlib.Tactic.Linarith
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.firstLowerPassageEqShiftedNegUpperPublic
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ) (x barrier : ℝ) :
    firstLowerPassage X x barrier =
      firstUpperPassage (fun t ω => -X t ω) (x - barrier) := by sorry
