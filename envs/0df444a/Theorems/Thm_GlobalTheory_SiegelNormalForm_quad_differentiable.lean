-- Prove2me | Theorems.Thm_GlobalTheory_SiegelNormalForm_quad_differentiable
-- name    : GlobalTheory.SiegelNormalForm.quad_differentiable
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:40.315854+00:00
-- url     : https://prove2.me/theorems/1304fa44-3ea0-4eba-8b8b-4d7a9ff2f4cc
-- title:
--   Siegel Normal Form: quad differentiable
-- statement:
--   The Siegel Normal Form construction uses the quad differentiable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/IsUnitOfLagrangian.lean#L155-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/IsUnitOfLagrangian.lean#L155-L159

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsUnitOfLagrangian
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
open GlobalTheory GlobalTheory.SiegelNormalForm
variable {g : ℕ}
open Complex Matrix Filter Topology
open scoped BigOperators Real
variable {g : ℕ}

theorem GlobalTheory.SiegelNormalForm.quad_differentiable (Y : Matrix (Fin g) (Fin g) ℂ)
    (c : Fin g → ℂ) : Differentiable ℂ (_root_.GlobalTheory.SiegelNormalForm.quad Y c) := by sorry
