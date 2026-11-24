-- Prove2me | Theorems.Thm_GlobalTheory_localization_isDomain_isIntegrallyClosed_of_finset_subring
-- name    : GlobalTheory.localization_isDomain_isIntegrallyClosed_of_finset_subring
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:08:14.207223+00:00
-- url     : https://prove2.me/theorems/6cbec21f-cbe5-4751-bdc4-2dd56b7998a3
-- title:
--   Global Theory: localization is Domain is Integrally Closed of finset subring
-- statement:
--   The Global Theory construction uses the localization is Domain is Integrally Closed of finset subring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LocalizationIsDomainIsIntegrallyClosedOfFinsetSu.lean#L191-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LocalizationIsDomainIsIntegrallyClosedOfFinsetSu.lean#L191-L196

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocalizationIsDomainIsIntegrallyClosedOfFinsetSu
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

theorem GlobalTheory.localization_isDomain_isIntegrallyClosed_of_finset_subring :
    ∀ (B : Type) [CommRing B] (Q : Ideal B) [Q.IsPrime], (∀ s : Finset B, ∃ C : Subring B, (↑s : Set B) ⊆ (C : Set B) ∧ ∀ (q : Ideal C) [q.IsPrime], IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q)) → IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q) := by sorry
