-- Prove2me | Theorems.Thm_GlobalTheory_Chow_aeval_smul_of_isHomogeneous
-- name    : GlobalTheory.Chow.aeval_smul_of_isHomogeneous
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:10:15.752846+00:00
-- url     : https://prove2.me/theorems/bd57ee16-ae4e-4400-a83e-1940d753dfe4
-- title:
--   Chow: aeval smul of is Homogeneous
-- statement:
--   The Chow construction uses the aeval smul of is Homogeneous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/AevalEqZeroOfHomogeneousComponent.lean#L139-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/AevalEqZeroOfHomogeneousComponent.lean#L139-L149

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

theorem GlobalTheory.Chow.aeval_smul_of_isHomogeneous {G : Type*} [CommRing G] [Algebra K G]
    {g : MvPolynomial σ K} {n : ℕ} (hg : g.IsHomogeneous n) (c : G) (ξ : σ → G) :
    aeval (fun j => c * ξ j) g = c ^ n * aeval ξ g := by sorry
