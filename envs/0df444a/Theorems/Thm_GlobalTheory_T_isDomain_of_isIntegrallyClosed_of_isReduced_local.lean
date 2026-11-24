-- Prove2me | Theorems.Thm_GlobalTheory_T_isDomain_of_isIntegrallyClosed_of_isReduced_local
-- name    : GlobalTheory.T.isDomain_of_isIntegrallyClosed_of_isReduced_local
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:48:08.342797+00:00
-- url     : https://prove2.me/theorems/170330fa-1e35-470a-970a-7d47cc94b0d0
-- title:
--   T: is Domain of is Integrally Closed of is Reduced local
-- statement:
--   The T construction uses the is Domain of is Integrally Closed of is Reduced local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsDomainOfIsIntegrallyClosedOfIsReducedStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsDomainOfIsIntegrallyClosedOfIsReducedStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsDomainOfIsIntegrallyClosedOfIsReduced
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsDomainOfIsIntegrallyClosedOfIsReducedStatement
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

theorem GlobalTheory.T.isDomain_of_isIntegrallyClosed_of_isReduced_local : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsReduced R], IsIntegrallyClosed R → IsDomain R := by sorry
