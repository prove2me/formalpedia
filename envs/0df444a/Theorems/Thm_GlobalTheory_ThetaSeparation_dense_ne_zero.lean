-- Prove2me | Theorems.Thm_GlobalTheory_ThetaSeparation_dense_ne_zero
-- name    : GlobalTheory.ThetaSeparation.dense_ne_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:14.023775+00:00
-- url     : https://prove2.me/theorems/a0bf6b6d-79d2-4adc-b6e8-3f43fbbc1544
-- title:
--   Theta Separation: dense ne zero
-- statement:
--   The Theta Separation construction uses the dense ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/LevelThreeSeparatesPoints.lean#L15-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/LevelThreeSeparatesPoints.lean#L15-L29

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_LevelThreeSeparatesPoints
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory GlobalTheory.ThetaSeparation
open Complex Matrix Filter Topology
open scoped BigOperators Real

theorem GlobalTheory.ThetaSeparation.dense_ne_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {f : E → ℂ} (hf : Differentiable ℂ f) (h0 : ∃ x, f x ≠ 0) :
    Dense {x | f x ≠ 0} := by sorry
