-- Prove2me | Theorems.Thm_GlobalTheory_isDomain_and_isIntegrallyClosed_atPrime_of_isDomain
-- name    : GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_of_isDomain
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:43:50.773896+00:00
-- url     : https://prove2.me/theorems/4ab6728a-898c-4dcd-a1a1-656465daff34
-- title:
--   Global Theory: is Domain and is Integrally Closed at Prime of is Domain
-- statement:
--   The Global Theory construction uses the is Domain and is Integrally Closed at Prime of is Domain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo.lean#L31-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo.lean#L31-L36

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

theorem GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_of_isDomain {B : Type*} [CommRing B] [IsDomain B]
    [IsIntegrallyClosed B] (p : Ideal B) [hp : p.IsPrime]
    (Bp : Type*) [CommRing Bp] [Algebra B Bp] [IsLocalization.AtPrime Bp p] :
    IsDomain Bp ∧ IsIntegrallyClosed Bp := by sorry
