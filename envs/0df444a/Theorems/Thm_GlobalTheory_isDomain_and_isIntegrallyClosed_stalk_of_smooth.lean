-- Prove2me | Theorems.Thm_GlobalTheory_isDomain_and_isIntegrallyClosed_stalk_of_smooth
-- name    : GlobalTheory.isDomain_and_isIntegrallyClosed_stalk_of_smooth
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:56:54.57486+00:00
-- url     : https://prove2.me/theorems/00f22822-1540-49f4-a8f0-5aee0dce40d2
-- title:
--   Global Theory: is Domain and is Integrally Closed stalk of smooth
-- statement:
--   The Global Theory construction uses the is Domain and is Integrally Closed stalk of smooth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo.lean#L202-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo.lean#L202-L219

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
open AlgebraicGeometry

theorem GlobalTheory.isDomain_and_isIntegrallyClosed_stalk_of_smooth {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f]
    (x : X) [IsDomain (Y.presheaf.stalk (f x))] [IsIntegrallyClosed (Y.presheaf.stalk (f x))] :
    IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x) := by sorry
