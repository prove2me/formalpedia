-- Prove2me | Theorems.Thm_GlobalTheory_Chow_ringKrullDim_eq_of_isIntegral
-- name    : GlobalTheory.Chow.ringKrullDim_eq_of_isIntegral
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:09:55.831357+00:00
-- url     : https://prove2.me/theorems/b84b03fa-9d9c-4ec3-bc16-8974b09a479c
-- title:
--   Chow: ring Krull Dim eq of is Integral
-- statement:
--   The Chow construction uses the ring Krull Dim eq of is Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsAlgebraicIndependentGenericPoint.lean#L16-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsAlgebraicIndependentGenericPoint.lean#L16-L27

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

theorem GlobalTheory.Chow.ringKrullDim_eq_of_isIntegral (R S : Type*) [CommRing R] [CommRing S] [IsDomain S]
    [Algebra R S] [FaithfulSMul R S] [Algebra.IsIntegral R S] :
    ringKrullDim S = ringKrullDim R := by sorry
