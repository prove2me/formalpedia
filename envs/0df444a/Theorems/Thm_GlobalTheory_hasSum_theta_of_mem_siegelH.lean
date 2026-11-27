-- Prove2me | Theorems.Thm_GlobalTheory_hasSum_theta_of_mem_siegelH
-- name    : GlobalTheory.hasSum_theta_of_mem_siegelH
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:47:03.924152+00:00
-- url     : https://prove2.me/theorems/7195e8dd-2630-5ca9-a721-ee5e9a3d2312
-- title:
--   Global Theory: has Sum theta of mem siegel H
-- statement:
--   The Global Theory construction uses the has Sum theta of mem siegel H property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsEventuallyNormRiemannThetaTermLe.lean#L792-L795
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsEventuallyNormRiemannThetaTermLe.lean#L792-L795

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

theorem GlobalTheory.hasSum_theta_of_mem_siegelH {τ : Matrix ι ι ℂ} (h : τ ∈ SiegelH ι)
    (a b : ι → ℝ) (z : ι → ℂ) :
    HasSum (thetaTerm a b z τ) (theta a b z τ) := by sorry
