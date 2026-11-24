-- Prove2me | Theorems.Thm_GlobalTheory_IsSiegel_natCast_smul
-- name    : GlobalTheory.IsSiegel.natCast_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:12.753865+00:00
-- url     : https://prove2.me/theorems/5d908717-fc5c-45b3-864c-f9318c0a73e7
-- title:
--   Is Siegel: nat Cast smul
-- statement:
--   The Is Siegel construction uses the nat Cast smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsEventuallyNormRiemannThetaTermLe.lean#L94-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsEventuallyNormRiemannThetaTermLe.lean#L94-L96

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

theorem GlobalTheory.IsSiegel.natCast_smul {Ω : Matrix ι ι ℂ} (h : IsSiegel Ω) {q : ℕ} (hq : 0 < q) :
    IsSiegel ((q : ℂ) • Ω) := by sorry
