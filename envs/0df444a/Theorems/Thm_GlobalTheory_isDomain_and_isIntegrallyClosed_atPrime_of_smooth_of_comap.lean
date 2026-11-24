-- Prove2me | Theorems.Thm_GlobalTheory_isDomain_and_isIntegrallyClosed_atPrime_of_smooth_of_comap
-- name    : GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_of_smooth_of_comap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:52:20.678071+00:00
-- url     : https://prove2.me/theorems/cd5c379a-82d4-447b-ac50-6617545d0a0d
-- title:
--   Global Theory: is Domain and is Integrally Closed at Prime of smooth of comap
-- statement:
--   The Global Theory construction uses the is Domain and is Integrally Closed at Prime of smooth of comap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo.lean#L160-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo.lean#L160-L175

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

theorem GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_of_smooth_of_comap {A B : Type*} [CommRing A]
    [CommRing B] [Algebra A B] [Algebra.Smooth A B] (p : Ideal B) [hp : p.IsPrime]
    (Ap : Type*) [CommRing Ap] [Algebra A Ap]
    [IsLocalization.AtPrime Ap (p.comap (algebraMap A B))] [IsDomain Ap] [IsIntegrallyClosed Ap]
    (Bp : Type*) [CommRing Bp] [Algebra B Bp] [IsLocalization.AtPrime Bp p] :
    IsDomain Bp ∧ IsIntegrallyClosed Bp := by sorry
