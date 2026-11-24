-- Prove2me | Theorems.Thm_GlobalTheory_isSiegel_iff_mem_siegelH
-- name    : GlobalTheory.isSiegel_iff_mem_siegelH
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:52:18.153136+00:00
-- url     : https://prove2.me/theorems/a32642bd-6c71-4c5b-a9fd-bbdf25251bd2
-- title:
--   Global Theory: is Siegel iff mem siegel H
-- statement:
--   The Global Theory construction uses the is Siegel iff mem siegel H property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsEventuallyNormRiemannThetaTermLe.lean#L15-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsEventuallyNormRiemannThetaTermLe.lean#L15-L16

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

theorem GlobalTheory.isSiegel_iff_mem_siegelH [Fintype ι] {Ω : Matrix ι ι ℂ} :
    IsSiegel Ω ↔ Ω ∈ ReciprocityTheory.PTheta.SiegelH ι := by sorry
