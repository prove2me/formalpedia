-- Prove2me | Theorems.Thm_GlobalTheory_CubeFrame_differentiableOn_prod_zpow
-- name    : GlobalTheory.CubeFrame.differentiableOn_prod_zpow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:59:37.011105+00:00
-- url     : https://prove2.me/theorems/cd819c53-80d1-482d-a005-14665e505cb3
-- title:
--   Cube Frame: differentiable On prod zpow
-- statement:
--   The Cube Frame construction uses the differentiable On prod zpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsGlobalFrameOfLocal.lean#L22-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsGlobalFrameOfLocal.lean#L22-L34

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

theorem GlobalTheory.CubeFrame.differentiableOn_prod_zpow {X α : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    {U : Set X} (s : Finset α) {f : α → X → ℂ} (e : α → ℤ)
    (hf : ∀ a ∈ s, DifferentiableOn ℂ (f a) U) (h0 : ∀ a ∈ s, ∀ x ∈ U, f a x ≠ 0) :
    DifferentiableOn ℂ (fun x => ∏ a ∈ s, f a x ^ e a) U := by sorry
