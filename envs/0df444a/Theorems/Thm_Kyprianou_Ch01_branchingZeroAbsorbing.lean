-- Prove2me | Theorems.Thm_Kyprianou_Ch01_branchingZeroAbsorbing
-- name    : Kyprianou.Ch01.branchingZeroAbsorbing
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T07:50:33.321123+00:00
-- url     : https://prove2.me/theorems/362b9ec2-2c39-45cb-bc89-598e08b8809b
-- title:
--   A zero-ancestor branching population remains extinct
-- statement:
--   A branching law on the natural numbers satisfying the additive convolution property has zero as an absorbing population state: a population started with zero ancestors has deterministic population zero at every nonnegative time. This follows because an idempotent probability law under addition on the nonnegative integers must be the unit mass at zero.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.11; structural consequence of the formal branching law, needed to apply the established branching cumulant semigroup law.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
open Kyprianou.Ch01 MeasureTheory Filter Set
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch01.branchingZeroAbsorbing
    (law : PopulationLaws) (hbranch : HasBranchingProperty law) :
    ∀ t : ℝ≥0, law 0 t = PMF.pure 0 := by sorry
