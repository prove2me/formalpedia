-- Prove2me | Theorems.Thm_Kyprianou_Ch05_exercise52CPDriverPathLawV1
-- name    : Kyprianou.Ch05.exercise52CPDriverPathLawV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T18:20:36.348693+00:00
-- url     : https://prove2.me/theorems/a10df5f5-4f25-417f-b071-41822dbb4759
-- title:
--   The comparison subordinator has the whole-path law of the canonical compound Poisson driver
-- statement:
--   The comparison subordinator has the whole-path law of the canonical compound Poisson driver
-- source:
--   Kyprianou (2006), Exercise 5.2(ii), renewal comparison

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

theorem Kyprianou.Ch05.exercise52CPDriverPathLawV1
    {Omega Lambda : Type} [MeasurableSpace Omega] [MeasurableSpace Lambda]
    (P : Measure Omega) [IsProbabilityMeasure P] (Q : Measure Lambda)
    [IsProbabilityMeasure Q]
    (X : NNReal → Omega → ℝ) (deathX : Omega → WithTop NNReal)
    (arrival marks : ℕ → Lambda → ℝ)
    (F : Measure ℝ) [IsProbabilityMeasure F] (hPos : F (Iic 0) = 0)
    (hd : LevyFoundations.IsCompoundPoissonDriver arrival marks 1 F Q)
    (hX : IsKilledSubordinator P X deathX 0)
    (hCP : ∀ (t : NNReal) (theta : ℝ), 0 ≤ theta →
      (∫ omega, Real.exp (-theta * X t omega) ∂P) =
        Real.exp (-(t : ℝ) * (∫ z in Ioi 0, (1 - Real.exp (-theta*z)) ∂F))) :
    P.map (fun w t => X t w) =
      Q.map (fun w (t : NNReal) => ProbabilityTheory.compoundPoisson 0 arrival marks (t : ℝ) w) := by
  sorry
