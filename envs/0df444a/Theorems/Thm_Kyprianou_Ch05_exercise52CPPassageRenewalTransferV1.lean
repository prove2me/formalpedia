-- Prove2me | Theorems.Thm_Kyprianou_Ch05_exercise52CPPassageRenewalTransferV1
-- name    : Kyprianou.Ch05.exercise52CPPassageRenewalTransferV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T17:31:13.075284+00:00
-- url     : https://prove2.me/theorems/0eb16a27-a16d-5b9e-8638-6d33648d9081
-- title:
--   The comparison process and positive compound Poisson driver have the same strict passage tail as the embedded renewal epochs
-- statement:
--   The comparison process and positive compound Poisson driver have the same strict passage tail as the embedded renewal epochs
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

theorem Kyprianou.Ch05.exercise52CPPassageRenewalTransferV1
    {Omega Lambda : Type} [MeasurableSpace Omega] [MeasurableSpace Lambda]
    (P : Measure Omega) [IsProbabilityMeasure P] (Q : Measure Lambda)
    [IsProbabilityMeasure Q]
    (X Xleft : NNReal → Omega → ℝ) (deathX : Omega → WithTop NNReal)
    (arrival marks : ℕ → Lambda → ℝ)
    (F : Measure ℝ) [IsProbabilityMeasure F] (hPos : F (Iic 0) = 0)
    (hd : LevyFoundations.IsCompoundPoissonDriver arrival marks 1 F Q)
    (hX : IsKilledSubordinator P X deathX 0)
    (hCP : ∀ (t : NNReal) (theta : ℝ), 0 ≤ theta →
      (∫ omega, Real.exp (-theta * X t omega) ∂P) =
        Real.exp (-(t : ℝ) * (∫ z in Ioi 0, (1 - Real.exp (-theta*z)) ∂F)))
    (hLeft : IsLeftLimitVersion P X Xleft) :
    ∀ x u y : ℝ, 0 < x → 0 < u → 0 < y →
      P {omega : Omega | PassageFinite X deathX x omega ∧
        passageOvershoot X deathX x omega ∈ Ioi u ∧
        passageUndershoot X Xleft deathX x omega ∈ Ioi y} =
      Q {w : Lambda | u < renewalOvershoot marks x w ∧
        y < renewalUndershoot marks x w} := by
  sorry
