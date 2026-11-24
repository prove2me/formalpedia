-- Prove2me | Theorems.Thm_GlobalTheory_isSiegel_unique_iff
-- name    : GlobalTheory.isSiegel_unique_iff
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:00:58.131895+00:00
-- url     : https://prove2.me/theorems/292b74c0-b833-4a88-93cf-a7c02a3edf98
-- title:
--   Global Theory: is Siegel unique iff
-- statement:
--   The Global Theory construction uses the is Siegel unique iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsEventuallyNormRiemannThetaTermLe.lean#L76-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsEventuallyNormRiemannThetaTermLe.lean#L76-L85

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

theorem GlobalTheory.isSiegel_unique_iff [Unique ι] {Ω : Matrix ι ι ℂ} :
    IsSiegel Ω ↔ 0 < (Ω default default).im := by sorry
