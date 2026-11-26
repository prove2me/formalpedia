-- Prove2me | Theorems.Thm_Kyprianou_Ch05_finitePositiveLevyMeasureNormalizeV1
-- name    : Kyprianou.Ch05.finitePositiveLevyMeasureNormalizeV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T13:02:48.581714+00:00
-- url     : https://prove2.me/theorems/7fd4960e-da58-5fd3-aca1-89c6120c6397
-- title:
--   Normalize a finite nonzero positive Levy measure to a probability mark law
-- statement:
--   Split the whole line into the positive half-line and its null complement, then normalize by the finite positive total mass.
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

theorem Kyprianou.Ch05.finitePositiveLevyMeasureNormalizeV1
    (Pi : Measure ℝ) (hs : Pi (Iic (0 : ℝ)) = 0)
    (hf : Pi (Ioi (0 : ℝ)) < ⊤) (hp : 0 < Pi (Ioi (0 : ℝ))) :
    ∃ (r : NNReal) (F : Measure ℝ), 0 < r ∧ IsProbabilityMeasure F ∧
      Pi = (r : ENNReal) • F := by
  sorry
