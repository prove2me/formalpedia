-- Prove2me | Theorems.Thm_GlobalTheory_T_adicCompletion_isDomain_and_isIntegrallyClosed
-- name    : GlobalTheory.T.adicCompletion_isDomain_and_isIntegrallyClosed
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T15:21:50.712802+00:00
-- url     : https://prove2.me/theorems/78576eaf-dcc8-537f-bbd4-d49f05568201
-- title:
--   T: adic Completion is Domain and is Integrally Closed
-- statement:
--   The T construction uses the adic Completion is Domain and is Integrally Closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/CompletionIsDomainAndIsIntegrallyClosedStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/CompletionIsDomainAndIsIntegrallyClosedStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_CompletionIsDomainAndIsIntegrallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_CompletionIsDomainAndIsIntegrallyClosedStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.adicCompletion_isDomain_and_isIntegrallyClosed : ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsIntegrallyClosed A] [CharZero A] [Algebra.EssFiniteType ℤ A], IsDomain (AdicCompletion (maximalIdeal A) A) ∧ IsIntegrallyClosed (AdicCompletion (maximalIdeal A) A) := by sorry
