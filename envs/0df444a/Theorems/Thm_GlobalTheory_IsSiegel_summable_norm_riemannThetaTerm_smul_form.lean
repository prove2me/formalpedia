-- Prove2me | Theorems.Thm_GlobalTheory_IsSiegel_summable_norm_riemannThetaTerm_smul_form
-- name    : GlobalTheory.IsSiegel.summable_norm_riemannThetaTerm_smul_form
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:11:23.013907+00:00
-- url     : https://prove2.me/theorems/43a2707a-b128-439d-8fe5-0fff84cda38c
-- title:
--   Is Siegel: summable norm riemann Theta Term smul form
-- statement:
--   The Is Siegel construction uses the summable norm riemann Theta Term smul form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsEventuallyNormRiemannThetaTermLe.lean#L431-L439
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsEventuallyNormRiemannThetaTermLe.lean#L431-L439

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

theorem GlobalTheory.IsSiegel.summable_norm_riemannThetaTerm_smul_form {Ω : Matrix ι ι ℂ} (h : IsSiegel Ω)
    (a b : ι → ℝ) (v : ι → ℂ) :
    Summable fun n => ‖riemannThetaTerm a b Ω v n • riemannThetaForm a n‖ := by sorry
