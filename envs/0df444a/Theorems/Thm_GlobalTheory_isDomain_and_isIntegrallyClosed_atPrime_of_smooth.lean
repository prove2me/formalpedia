-- Prove2me | Theorems.Thm_GlobalTheory_isDomain_and_isIntegrallyClosed_atPrime_of_smooth
-- name    : GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_of_smooth
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:26:22.679507+00:00
-- url     : https://prove2.me/theorems/9656115a-b7eb-4991-bb11-c78dd0004cb3
-- title:
--   Global Theory: is Domain and is Integrally Closed at Prime of smooth
-- statement:
--   The Global Theory construction uses the is Domain and is Integrally Closed at Prime of smooth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo.lean#L147-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo.lean#L147-L158

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
universe u
open GlobalTheory

theorem GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_of_smooth (A : Type*) {B : Type*} [CommRing A]
    [CommRing B] [IsDomain A] [IsIntegrallyClosed A] [Algebra A B] [Algebra.Smooth A B]
    (p : Ideal B) [hp : p.IsPrime]
    (Bp : Type*) [CommRing Bp] [Algebra B Bp] [IsLocalization.AtPrime Bp p] :
    IsDomain Bp ∧ IsIntegrallyClosed Bp := by sorry
