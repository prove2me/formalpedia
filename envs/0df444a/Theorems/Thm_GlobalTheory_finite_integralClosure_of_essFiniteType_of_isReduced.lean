-- Prove2me | Theorems.Thm_GlobalTheory_finite_integralClosure_of_essFiniteType_of_isReduced
-- name    : GlobalTheory.finite_integralClosure_of_essFiniteType_of_isReduced
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:59:53.426114+00:00
-- url     : https://prove2.me/theorems/d83725c8-1e1d-45ce-8c48-f41a3da6bf76
-- title:
--   Global Theory: finite integral Closure of ess Finite Type of is Reduced
-- statement:
--   The Global Theory construction uses the finite integral Closure of ess Finite Type of is Reduced property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteIntegralClosureOfEssFiniteTypeField.lean#L452-L474
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteIntegralClosureOfEssFiniteTypeField.lean#L452-L474

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsFormsAlgebraicIndependentSmulSubSumMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SubalgebraEqBotOfIsIntegralOfIsIntegrallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteIntegralClosureOfEssFiniteTypeField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Polynomial
variable (o R : Type*) [CommRing o] [IsDedekindDomain o] [CommRing R] [Algebra o R]
  [Algebra.FiniteType o R]
include o

theorem GlobalTheory.finite_integralClosure_of_essFiniteType_of_isReduced (B : Type*) [CommRing B]
    [IsReduced B] [IsAddTorsionFree B] [Algebra R B] [Algebra.EssFiniteType R B] :
    Module.Finite R (integralClosure R B) := by sorry
