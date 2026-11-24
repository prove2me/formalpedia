-- Prove2me | Theorems.Thm_GlobalTheory_isDomain_of_isIntegrallyClosed_of_isReduced
-- name    : GlobalTheory.isDomain_of_isIntegrallyClosed_of_isReduced
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T22:57:06.971742+00:00
-- url     : https://prove2.me/theorems/f51ec2f2-7f7e-46ce-8938-b03eb6629ed3
-- title:
--   Global Theory: is Domain of is Integrally Closed of is Reduced
-- statement:
--   The Global Theory construction uses the is Domain of is Integrally Closed of is Reduced property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsDomainOfIsIntegrallyClosedOfIsReduced.lean#L18-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsDomainOfIsIntegrallyClosedOfIsReduced.lean#L18-L113

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsDomainOfIsIntegrallyClosedOfIsReduced
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory

theorem GlobalTheory.isDomain_of_isIntegrallyClosed_of_isReduced :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsReduced R],
      IsIntegrallyClosed R → IsDomain R := by sorry
