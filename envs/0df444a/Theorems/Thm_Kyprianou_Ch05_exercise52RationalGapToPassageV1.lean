-- Prove2me | Theorems.Thm_Kyprianou_Ch05_exercise52RationalGapToPassageV1
-- name    : Kyprianou.Ch05.exercise52RationalGapToPassageV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:27:43.670048+00:00
-- url     : https://prove2.me/theorems/638099fa-420d-44c7-974c-1dbf1e5386fa
-- title:
--   A rational gap gives both strict passage margins at the first passage
-- statement:
--   A rational gap gives both strict passage margins at the first passage
-- source:
--   Kyprianou (2006), Exercise 5.2(ii)

import Mathlib
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_Kyprianou_Ch05_RenewalEpochProcess
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch05_RiskConditionalPassage
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

open Set
open Kyprianou.Ch05

open Topology

theorem Kyprianou.Ch05.exercise52RationalGapToPassageV1
    (Y L : NNReal → ℝ) (hm : Monotone Y)
    (s : NNReal) (hs0 : 0 < s)
    (hl : Tendsto Y (nhdsWithin s (Iio s)) (nhds (L s)))
    (x u y : ℝ) (hx : 0 < x) (hu : 0 < u) (hy : 0 < y)
    (hr : ∀ t, ContinuousWithinAt Y (Ici t) t)
    (hpre : ∀ t, t < s → Y t ≤ x) (hat : x ≤ Y s)
    (hgap : (∃ a b : ℚ, (a : ℝ) < x-y ∧ x+u < (b : ℝ) ∧
      (∀ q : ℚ, Y (Real.toNNReal q) ≤ (a : ℝ) ∨ (b : ℝ) ≤ Y (Real.toNNReal q)) ∧
      ∃ q : ℚ, (b : ℝ) ≤ Y (Real.toNNReal q))) :
    u < Y s - x ∧ y < x - L s := by
  sorry
