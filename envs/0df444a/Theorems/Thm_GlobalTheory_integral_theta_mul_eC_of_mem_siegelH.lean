-- Prove2me | Theorems.Thm_GlobalTheory_integral_theta_mul_eC_of_mem_siegelH
-- name    : GlobalTheory.integral_theta_mul_eC_of_mem_siegelH
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:46:50.133526+00:00
-- url     : https://prove2.me/theorems/f86d0aa8-7fc8-5555-a782-a302b6af59d3
-- title:
--   Global Theory: integral theta mul e C of mem siegel H
-- statement:
--   The Global Theory construction uses the integral theta mul e C of mem siegel H property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsEventuallyNormRiemannThetaTermLe.lean#L810-L817
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsEventuallyNormRiemannThetaTermLe.lean#L810-L817

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_PeriodLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology MeasureTheory
open scoped Real
noncomputable section
open GlobalTheory
variable {ι κ : Type*}
variable [Fintype ι] [Fintype κ]
open ReciprocityTheory.PTheta

theorem GlobalTheory.integral_theta_mul_eC_of_mem_siegelH {τ : Matrix ι ι ℂ} (h : τ ∈ SiegelH ι)
    (a b : ι → ℝ) (z : ι → ℂ) (l : ι → ℤ) :
    ∫ x in Set.Icc (0 : ι → ℝ) 1, theta a b (z + ofRealVec x) τ *
        eC (-(shiftVec a l ⬝ᵥ ofRealVec x)) = thetaTerm a b z τ l := by sorry
