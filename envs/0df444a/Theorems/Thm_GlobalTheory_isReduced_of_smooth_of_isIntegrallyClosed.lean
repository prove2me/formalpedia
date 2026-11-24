-- Prove2me | Theorems.Thm_GlobalTheory_isReduced_of_smooth_of_isIntegrallyClosed
-- name    : GlobalTheory.isReduced_of_smooth_of_isIntegrallyClosed
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T11:43:34.060191+00:00
-- url     : https://prove2.me/theorems/a0f0c9c2-ff70-40d6-ac0e-0b6d9a521668
-- title:
--   Global Theory: is Reduced of smooth of is Integrally Closed
-- statement:
--   The Global Theory construction uses the is Reduced of smooth of is Integrally Closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo.lean#L194-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo.lean#L194-L198

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

theorem GlobalTheory.isReduced_of_smooth_of_isIntegrallyClosed (A B : Type*) [CommRing A] [CommRing B]
    [IsDomain A] [IsIntegrallyClosed A] [Algebra A B] [Algebra.Smooth A B] : IsReduced B := by sorry
