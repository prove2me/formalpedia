-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reverseIntegerCompoundPoissonConstantBeforeFirstArrival
-- name    : Kyprianou.Ch01.reverseIntegerCompoundPoissonConstantBeforeFirstArrival
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T11:36:00.487682+00:00
-- url     : https://prove2.me/theorems/9ec7b674-f062-4db2-aa6c-044530c172f1
-- title:
--   Integer-valued reverse Lamperti compound-Poisson surplus remains at its initial state before first jump
-- statement:
--   For any natural initial population y and any raw compound-Poisson interarrival and mark paths, the integerCompoundPoisson surplus equals exactly y at every nonnegative raw time strictly before the first arrival. This follows from the existing public Proved AvramDividend.Classical.avram_jump6_A_actual_compoundPoisson_zero_before_first_physical_mark_any_clock and the definition as Int.floor(y+compoundPoisson). No distributional, positivity or finite-moment hypothesis is needed.
-- source:
--   Direct reuse of public Proved AvramDividend.Classical.avram_jump6_A_actual_compoundPoisson_zero_before_first_physical_mark_any_clock UUID 17227efd-426c-419e-9846-76e09a778cd5 in Kyprianou (2006) Chapter 1 discrete inverse Lamperti.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.reverseIntegerCompoundPoissonConstantBeforeFirstArrival
    {Ω : Type*} [MeasurableSpace Ω]
    (y : ℕ) (arrival marks : ℕ → Ω → ℝ)
    (t : ℝ≥0) (ω : Ω)
    (hBefore : (t : ℝ) < ProbabilityTheory.arrival arrival 0 ω) :
    integerCompoundPoisson y arrival marks t ω = (y : ℤ) := by
  sorry
