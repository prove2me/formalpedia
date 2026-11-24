-- Prove2me | Theorems.Thm_GlobalTheory_isDomain_and_isIntegrallyClosed_atPrime_of_isIntegrallyClosedIn_pi
-- name    : GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_of_isIntegrallyClosedIn_pi
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:56:55.665571+00:00
-- url     : https://prove2.me/theorems/6e5687b5-f8e2-4fa1-9f61-1a4cf822fcbd
-- title:
--   Global Theory: is Domain and is Integrally Closed at Prime of is Integrally Closed In pi
-- statement:
--   The Global Theory construction uses the is Domain and is Integrally Closed at Prime of is Integrally Closed In pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo.lean#L38-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo.lean#L38-L95

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

theorem GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_of_isIntegrallyClosedIn_pi {B : Type*} [CommRing B]
    {ι : Type*} [Finite ι] (K : ι → Type*) [∀ i, Field (K i)] [Algebra B (Π i, K i)]
    [hB : IsIntegrallyClosedIn B (Π i, K i)] (p : Ideal B) [hp : p.IsPrime]
    (Bp : Type*) [CommRing Bp] [Algebra B Bp] [IsLocalization.AtPrime Bp p] :
    IsDomain Bp ∧ IsIntegrallyClosed Bp := by sorry
