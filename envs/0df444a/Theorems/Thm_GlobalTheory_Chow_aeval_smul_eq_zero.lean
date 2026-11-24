-- Prove2me | Theorems.Thm_GlobalTheory_Chow_aeval_smul_eq_zero
-- name    : GlobalTheory.Chow.aeval_smul_eq_zero
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:09:56.376116+00:00
-- url     : https://prove2.me/theorems/170e5ca7-1184-4fb2-8882-85938e62ed05
-- title:
--   Chow: aeval smul eq zero
-- statement:
--   The Chow construction uses the aeval smul eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/AevalEqZeroOfHomogeneousComponent.lean#L157-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/AevalEqZeroOfHomogeneousComponent.lean#L157-L163

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_WeightedHomogeneousComponentMemElimIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_AevalEqZeroOfHomogeneousComponent
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
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K : Type*} [CommRing K] {σ β : Type*}

theorem GlobalTheory.Chow.aeval_smul_eq_zero {G : Type*} [CommRing G] [Algebra K G]
    {p : Ideal (MvPolynomial σ K)} (hp : p.IsHomogeneous (homogeneousSubmodule σ K))
    {ξ : σ → G} (hξ : ∀ g ∈ p, aeval ξ g = 0) (c : G) :
    ∀ g ∈ p, aeval (fun j => c * ξ j) g = 0 := by sorry
