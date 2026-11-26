-- Prove2me | Theorems.Thm_Kyprianou_Ch05_exercise52DriverLaplaceV1
-- name    : Kyprianou.Ch05.exercise52DriverLaplaceV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:41:49.757632+00:00
-- url     : https://prove2.me/theorems/3c61b72e-5819-4037-93d3-707ee6acc424
-- title:
--   The driftless positive compound Poisson driver has the comparison Laplace transform
-- statement:
--   The driftless positive compound Poisson driver has the comparison Laplace transform
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

theorem Kyprianou.Ch05.exercise52DriverLaplaceV1
    {Lambda : Type} [MeasurableSpace Lambda] (Q : Measure Lambda)
    [IsProbabilityMeasure Q] (arrival marks : ℕ → Lambda → ℝ)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hd : LevyFoundations.IsCompoundPoissonDriver arrival marks 1 F Q)
    (hPos : F (Iic 0) = 0) (t : NNReal) (theta : ℝ) (hTheta : 0 ≤ theta) :
    (∫ w, Real.exp (-theta * ProbabilityTheory.compoundPoisson 0 arrival marks
        (t : ℝ) w) ∂Q) =
      Real.exp (-(t : ℝ) * (∫ z in Ioi 0, (1 - Real.exp (-theta*z)) ∂F)) := by
  sorry
