-- Prove2me | Theorems.Thm_Kyprianou_Ch05_exercise52RationalJumpCountSurjectiveV1
-- name    : Kyprianou.Ch05.exercise52RationalJumpCountSurjectiveV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:31:39.618285+00:00
-- url     : https://prove2.me/theorems/f3bb5ed2-01de-5264-b51f-fa2c8eb0b2e7
-- title:
--   Regular positive arrival times attain every jump count at a rational time
-- statement:
--   Regular positive arrival times attain every jump count at a rational time
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

theorem Kyprianou.Ch05.exercise52RationalJumpCountSurjectiveV1
    (T : ℕ → ℝ) (hmono : StrictMono T) (htop : Tendsto T atTop atTop)
    (h0 : 0 < T 0) :
    Function.Surjective (fun q : ℚ => ProbabilityTheory.jumpCount T
      (Real.toNNReal q : ℝ)) := by
  sorry
