-- Prove2me | Theorems.Thm_GlobalTheory_isDomain_and_isIntegrallyClosed_atPrime_of_isLocalization
-- name    : GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_of_isLocalization
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:26:14.020822+00:00
-- url     : https://prove2.me/theorems/4118f5f3-20a2-4438-a94d-e6221d64f719
-- title:
--   Global Theory: is Domain and is Integrally Closed at Prime of is Localization
-- statement:
--   The Global Theory construction uses the is Domain and is Integrally Closed at Prime of is Localization property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo.lean#L9-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo.lean#L9-L29

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

theorem GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_of_isLocalization {B : Type*} [CommRing B]
    (M : Submonoid B) (T : Type*) [CommRing T] [Algebra B T] [IsLocalization M T]
    (p : Ideal B) [hp : p.IsPrime] (hM : Disjoint (M : Set B) (p : Set B))
    (h : ∀ (q : Ideal T) [q.IsPrime],
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q))
    (Bp : Type*) [CommRing Bp] [Algebra B Bp] [IsLocalization.AtPrime Bp p] :
    IsDomain Bp ∧ IsIntegrallyClosed Bp := by sorry
