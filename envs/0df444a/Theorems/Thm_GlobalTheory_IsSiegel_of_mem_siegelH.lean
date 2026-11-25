-- Prove2me | Theorems.Thm_GlobalTheory_IsSiegel_of_mem_siegelH
-- name    : GlobalTheory.IsSiegel.of_mem_siegelH
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:11:09.027798+00:00
-- url     : https://prove2.me/theorems/b0517dbc-c81e-5acc-896d-71ce45f5d7f9
-- title:
--   Is Siegel: of mem siegel H
-- statement:
--   The Is Siegel construction uses the of mem siegel H property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsEventuallyNormRiemannThetaTermLe.lean#L28-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsEventuallyNormRiemannThetaTermLe.lean#L28-L29

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

theorem GlobalTheory.IsSiegel.of_mem_siegelH [Fintype ι] {Ω : Matrix ι ι ℂ}
    (h : Ω ∈ ReciprocityTheory.PTheta.SiegelH ι) : IsSiegel Ω := by sorry
