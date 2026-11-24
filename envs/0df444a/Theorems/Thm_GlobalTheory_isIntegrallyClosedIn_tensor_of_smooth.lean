-- Prove2me | Theorems.Thm_GlobalTheory_isIntegrallyClosedIn_tensor_of_smooth
-- name    : GlobalTheory.isIntegrallyClosedIn_tensor_of_smooth
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:56:48.229855+00:00
-- url     : https://prove2.me/theorems/c58bac73-52c7-49b6-92c3-f2f63d27d984
-- title:
--   Global Theory: is Integrally Closed In tensor of smooth
-- statement:
--   The Global Theory construction uses the is Integrally Closed In tensor of smooth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo.lean#L97-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo.lean#L97-L120

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

theorem GlobalTheory.isIntegrallyClosedIn_tensor_of_smooth {A B L : Type*} [CommRing A] [CommRing B]
    [CommRing L] [Algebra A B] [Algebra A L] [Algebra.Smooth A B] [hL : IsIntegrallyClosedIn A L] :
    IsIntegrallyClosedIn B (B ⊗[A] L) := by sorry
