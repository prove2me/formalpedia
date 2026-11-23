-- Prove2me | Theorems.Thm_GlobalTheory_forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth
-- name    : GlobalTheory.forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:51:52.62931+00:00
-- url     : https://prove2.me/theorems/eb6aac32-a9dc-4eaa-a200-ff2385b9a41d
-- title:
--   Global Theory: forall is Domain and is Integrally Closed stalk of smooth
-- statement:
--   The Global Theory construction uses the forall is Domain and is Integrally Closed stalk of smooth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo.lean#L223-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo.lean#L223-L229

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

theorem GlobalTheory.forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Smooth f]
    (hY : ∀ y : Y, IsDomain (Y.presheaf.stalk y) ∧ IsIntegrallyClosed (Y.presheaf.stalk y))
    (x : X) : IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x) := by sorry
