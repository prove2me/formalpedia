-- Prove2me | Theorems.Thm_GlobalTheory_Chow_isPrincipal_of_forall_C_mem
-- name    : GlobalTheory.Chow.isPrincipal_of_forall_C_mem
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T11:09:55.124673+00:00
-- url     : https://prove2.me/theorems/08fad4c8-3897-43b8-b789-0fc96299e61b
-- title:
--   Chow: is Principal of forall C mem
-- statement:
--   The Chow construction uses the is Principal of forall C mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsAlgebraicIndependentGenericPoint.lean#L48-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsAlgebraicIndependentGenericPoint.lean#L48-L71

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_AevalEqZeroOfHomogeneousComponent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsAlgebraicIndependentGenericPoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.Chow
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] Polynomial.algebra Polynomial.isLocalization

theorem GlobalTheory.Chow.isPrincipal_of_forall_C_mem {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] (E : Ideal (Polynomial R)) [hE : E.IsPrime]
    (h : ∀ r, Polynomial.C r ∈ E → r = 0) : E.IsPrincipal := by sorry
