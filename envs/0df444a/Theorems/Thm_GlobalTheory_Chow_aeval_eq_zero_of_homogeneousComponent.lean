-- Prove2me | Theorems.Thm_GlobalTheory_Chow_aeval_eq_zero_of_homogeneousComponent
-- name    : GlobalTheory.Chow.aeval_eq_zero_of_homogeneousComponent
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:15:12.911215+00:00
-- url     : https://prove2.me/theorems/9847e455-f018-4bf2-b6bf-7f7573f23741
-- title:
--   Chow: aeval eq zero of homogeneous Component
-- statement:
--   The Chow construction uses the aeval eq zero of homogeneous Component property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/AevalEqZeroOfHomogeneousComponent.lean#L151-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/AevalEqZeroOfHomogeneousComponent.lean#L151-L155

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

theorem GlobalTheory.Chow.aeval_eq_zero_of_homogeneousComponent {G : Type*} [CommRing G] [Algebra K G]
    {g : MvPolynomial σ K} {ξ : σ → G} (h : ∀ n, aeval ξ (homogeneousComponent n g) = 0) :
    aeval ξ g = 0 := by sorry
