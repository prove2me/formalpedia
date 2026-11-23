-- Prove2me | Theorems.Thm_GlobalTheory_CubeFrame_differentiableOn_div
-- name    : GlobalTheory.CubeFrame.differentiableOn_div
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:59:39.664887+00:00
-- url     : https://prove2.me/theorems/c04be0d1-b5b1-43c2-9a01-3fc90ea48d14
-- title:
--   Cube Frame: differentiable On div
-- statement:
--   The Cube Frame construction uses the differentiable On div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsGlobalFrameOfLocal.lean#L36-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsGlobalFrameOfLocal.lean#L36-L40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsGlobalFrameOfLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory GlobalTheory.CubeFrame

theorem GlobalTheory.CubeFrame.differentiableOn_div {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    {U : Set X} {f g : X → ℂ} (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    (h0 : ∀ x ∈ U, g x ≠ 0) : DifferentiableOn ℂ (fun x => f x / g x) U := by sorry
