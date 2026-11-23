-- Prove2me | Theorems.Thm_GlobalTheory_integralClosure_restrictScalars_of_isIntegral
-- name    : GlobalTheory.integralClosure_restrictScalars_of_isIntegral
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:14:17.363171+00:00
-- url     : https://prove2.me/theorems/16d0af68-7976-44af-8c25-6f1fbc272b4e
-- title:
--   Global Theory: integral Closure restrict Scalars of is Integral
-- statement:
--   The Global Theory construction uses the integral Closure restrict Scalars of is Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SubalgebraEqBotOfIsIntegralOfIsIntegrallyClosed.lean#L9-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SubalgebraEqBotOfIsIntegralOfIsIntegrallyClosed.lean#L9-L15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SubalgebraEqBotOfIsIntegralOfIsIntegrallyClosed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped PowerSeries TensorProduct
open GlobalTheory
open scoped PowerSeries TensorProduct

theorem GlobalTheory.integralClosure_restrictScalars_of_isIntegral (A A' B : Type*) [CommRing A] [CommRing A']
    [CommRing B] [Algebra A A'] [Algebra A' B] [Algebra A B] [IsScalarTower A A' B]
    [Algebra.IsIntegral A A'] :
    (integralClosure A' B).restrictScalars A = integralClosure A B := by sorry
