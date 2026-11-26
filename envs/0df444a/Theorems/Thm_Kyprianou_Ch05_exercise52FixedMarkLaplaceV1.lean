-- Prove2me | Theorems.Thm_Kyprianou_Ch05_exercise52FixedMarkLaplaceV1
-- name    : Kyprianou.Ch05.exercise52FixedMarkLaplaceV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:41:47.494793+00:00
-- url     : https://prove2.me/theorems/ec7fbc1e-8e3b-4430-b05b-51f423fc6559
-- title:
--   Independent identically distributed marks have a factorised finite-sum Laplace moment
-- statement:
--   Independent identically distributed marks have a factorised finite-sum Laplace moment
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

theorem Kyprianou.Ch05.exercise52FixedMarkLaplaceV1
    {Lambda : Type} [MeasurableSpace Lambda] (Q : Measure Lambda)
    [IsProbabilityMeasure Q] (arrival marks : ℕ → Lambda → ℝ)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hd : LevyFoundations.IsCompoundPoissonDriver arrival marks 1 F Q) (k : ℕ) (theta : ℝ) :
    (∫ w, Real.exp (theta * ∑ i ∈ Finset.range k, marks i w) ∂Q) =
      (∫ z, Real.exp (theta*z) ∂F)^k := by
  sorry
