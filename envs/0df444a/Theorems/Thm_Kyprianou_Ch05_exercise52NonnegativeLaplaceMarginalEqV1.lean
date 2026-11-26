-- Prove2me | Theorems.Thm_Kyprianou_Ch05_exercise52NonnegativeLaplaceMarginalEqV1
-- name    : Kyprianou.Ch05.exercise52NonnegativeLaplaceMarginalEqV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:41:44.453964+00:00
-- url     : https://prove2.me/theorems/9d41b99e-aa00-54bf-ab53-cf6408db86b7
-- title:
--   Nonnegative random variables with matching real Laplace moments have identical pushforward laws
-- statement:
--   Nonnegative random variables with matching real Laplace moments have identical pushforward laws
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

theorem Kyprianou.Ch05.exercise52NonnegativeLaplaceMarginalEqV1
    {Omega Lambda : Type} [MeasurableSpace Omega] [MeasurableSpace Lambda]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Q : Measure Lambda) [IsProbabilityMeasure Q]
    (A : Omega → ℝ) (B : Lambda → ℝ)
    (ha : AEMeasurable A P) (hb : AEMeasurable B Q)
    (hpa : ∀ᵐ w ∂P, 0 ≤ A w) (hpb : ∀ᵐ w ∂Q, 0 ≤ B w)
    (hEq : ∀ theta : ℝ, 0 < theta →
      (∫ w, Real.exp (-theta*A w) ∂P) = (∫ w, Real.exp (-theta*B w) ∂Q)) :
    P.map A = Q.map B := by
  sorry
