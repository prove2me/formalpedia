-- Prove2me | Theorems.Thm_GlobalTheory_Chow_injective_of_constantCoeff
-- name    : GlobalTheory.Chow.injective_of_constantCoeff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:10:09.563506+00:00
-- url     : https://prove2.me/theorems/766c68ba-c867-4a0e-aa6b-643a00e77d07
-- title:
--   Chow: injective of constant Coeff
-- statement:
--   The Chow construction uses the injective of constant Coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsAlgebraicIndependentGenericPoint.lean#L96-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsAlgebraicIndependentGenericPoint.lean#L96-L116

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

theorem GlobalTheory.Chow.injective_of_constantCoeff {R S V : Type*} [CommRing R] [CommRing S]
    (ψ : MvPolynomial V R →+* MvPolynomial V S) (hX : ∀ v, ψ (X v) = X v)
    (h : ∀ r, constantCoeff (ψ (C r)) = 0 → r = 0) : Function.Injective ψ := by sorry
