-- Prove2me | Theorems.Thm_GlobalTheory_T_isDomain_isIntegrallyClosed_atPrime_of_finset_subrings
-- name    : GlobalTheory.T.isDomain_isIntegrallyClosed_atPrime_of_finset_subrings
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:34:21.6768+00:00
-- url     : https://prove2.me/theorems/4051eded-7e63-4f16-a4f4-9d6453de00a2
-- title:
--   T: is Domain is Integrally Closed at Prime of finset subrings
-- statement:
--   The T construction uses the is Domain is Integrally Closed at Prime of finset subrings property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LocalizationIsDomainIsIntegrallyClosedOfFinsetSuStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LocalizationIsDomainIsIntegrallyClosedOfFinsetSuStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocalizationIsDomainIsIntegrallyClosedOfFinsetSu
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocalizationIsDomainIsIntegrallyClosedOfFinsetSuStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.isDomain_isIntegrallyClosed_atPrime_of_finset_subrings : ∀ (B : Type) [CommRing B] (Q : Ideal B) [Q.IsPrime], (∀ s : Finset B, ∃ C : Subring B, (↑s : Set B) ⊆ (C : Set B) ∧ ∀ (q : Ideal C) [q.IsPrime], IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q)) → IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q) := by sorry
