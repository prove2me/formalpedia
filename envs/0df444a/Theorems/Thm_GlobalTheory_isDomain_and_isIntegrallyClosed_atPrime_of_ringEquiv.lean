-- Prove2me | Theorems.Thm_GlobalTheory_isDomain_and_isIntegrallyClosed_atPrime_of_ringEquiv
-- name    : GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_of_ringEquiv
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:57:08.158065+00:00
-- url     : https://prove2.me/theorems/33254e3f-91ba-4dba-8f2f-4309d83389c1
-- title:
--   Global Theory: is Domain and is Integrally Closed at Prime of ring Equiv
-- statement:
--   The Global Theory construction uses the is Domain and is Integrally Closed at Prime of ring Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsDomainAndIsIntegrallyClosedAtPrimeTensorFieldA.lean#L7-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsDomainAndIsIntegrallyClosedAtPrimeTensorFieldA.lean#L7-L27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsDomainAndIsIntegrallyClosedAtPrimeTensorFieldA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory

theorem GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_of_ringEquiv {D C : Type*} [CommRing D]
    [CommRing C] (e : D ≃+* C)
    (h : ∀ (q : Ideal D) [q.IsPrime],
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q))
    (q : Ideal C) [hq : q.IsPrime] :
    IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) := by sorry
