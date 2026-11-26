-- Prove2me | Theorems.Thm_Kyprianou_Ch05_exercise52CPDriverRenewalEpochV1
-- name    : Kyprianou.Ch05.exercise52CPDriverRenewalEpochV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T17:31:03.265771+00:00
-- url     : https://prove2.me/theorems/034b88a5-ecb3-5fbc-9a86-1488cc11c88d
-- title:
--   The marks of a positive compound Poisson driver form a renewal epoch process
-- statement:
--   The marks of a positive compound Poisson driver form a renewal epoch process
-- source:
--   Kyprianou (2006), Exercise 5.2, Lemma 5.5

import Mathlib
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

theorem Kyprianou.Ch05.exercise52CPDriverRenewalEpochV1
    {Lambda : Type} [MeasurableSpace Lambda] (Q : Measure Lambda)
    [IsProbabilityMeasure Q] (arrival marks : ℕ → Lambda → ℝ)
    (F : Measure ℝ) [IsProbabilityMeasure F] (hPos : F (Iic 0) = 0)
    (hd : LevyFoundations.IsCompoundPoissonDriver arrival marks 1 F Q) :
    IsRenewalEpochProcess Q marks F := by
  sorry
