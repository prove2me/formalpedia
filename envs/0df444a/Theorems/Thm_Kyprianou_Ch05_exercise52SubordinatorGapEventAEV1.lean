-- Prove2me | Theorems.Thm_Kyprianou_Ch05_exercise52SubordinatorGapEventAEV1
-- name    : Kyprianou.Ch05.exercise52SubordinatorGapEventAEV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:20:22.281937+00:00
-- url     : https://prove2.me/theorems/af62b040-a83c-5887-91f8-5760b2042826
-- title:
--   The positive-axis passage tail of an unkilled subordinator equals its rational gap event almost surely
-- statement:
--   The positive-axis passage tail of an unkilled subordinator equals its rational gap event almost surely
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

theorem Kyprianou.Ch05.exercise52SubordinatorGapEventAEV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X Xleft : NNReal → Omega → ℝ) (deathX : Omega → WithTop NNReal)
    (hX : IsKilledSubordinator P X deathX 0)
    (hLeft : IsLeftLimitVersion P X Xleft)
    (x u y : ℝ) (hx : 0 < x) (hu : 0 < u) (hy : 0 < y) :
    ∀ᵐ w ∂P,
      (PassageFinite X deathX x w ∧ passageOvershoot X deathX x w ∈ Ioi u ∧
        passageUndershoot X Xleft deathX x w ∈ Ioi y) ↔
      (fun t => X t w) ∈ {g : NNReal → ℝ | ∃ a b : ℚ, (a : ℝ) < x - y ∧ x + u < (b : ℝ) ∧
      (∀ q : ℚ, g (Real.toNNReal q) ≤ (a : ℝ) ∨ (b : ℝ) ≤ g (Real.toNNReal q)) ∧
      ∃ q : ℚ, (b : ℝ) ≤ g (Real.toNNReal q)} := by
  sorry
