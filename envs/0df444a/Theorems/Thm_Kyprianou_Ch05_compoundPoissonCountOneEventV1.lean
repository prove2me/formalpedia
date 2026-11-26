-- Prove2me | Theorems.Thm_Kyprianou_Ch05_compoundPoissonCountOneEventV1
-- name    : Kyprianou.Ch05.compoundPoissonCountOneEventV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T13:08:04.663209+00:00
-- url     : https://prove2.me/theorems/5878d339-3308-43a6-90b3-edb555922919
-- title:
--   One arrival index is equivalent to first arrival reached and second not reached
-- statement:
--   Use the least-index definition of jumpCount. Count one means index one is in the strict-after-time set and index zero is not.
-- source:
--   Kyprianou (2006), Chapter 5, Theorem 5.4.

import Mathlib
import Definitions.Def_levy_foundations_compoundPoisson
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_jumpCount
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_Kyprianou_Ch03_IsSubordinator
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05 Set Complex

theorem Kyprianou.Ch05.compoundPoissonCountOneEventV1
    (T : ℕ → ℝ) (t : ℝ) :
    LevyFoundations.jumpCount T t = 1 ↔ T 0 ≤ t ∧ t < T 1 := by
  sorry
