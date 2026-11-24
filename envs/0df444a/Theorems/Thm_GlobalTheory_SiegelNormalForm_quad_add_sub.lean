-- Prove2me | Theorems.Thm_GlobalTheory_SiegelNormalForm_quad_add_sub
-- name    : GlobalTheory.SiegelNormalForm.quad_add_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:47.037911+00:00
-- url     : https://prove2.me/theorems/a25666c5-1436-4f17-b93c-c937b6244f6b
-- title:
--   Siegel Normal Form: quad add sub
-- statement:
--   The Siegel Normal Form construction uses the quad add sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/IsUnitOfLagrangian.lean#L164-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/IsUnitOfLagrangian.lean#L164-L171

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

theorem GlobalTheory.SiegelNormalForm.quad_add_sub {Y : Matrix (Fin g) (Fin g) ℂ} (hY : Y.IsSymm)
    (c z w : Fin g → ℂ) :
    _root_.GlobalTheory.SiegelNormalForm.quad Y c (z + w) - _root_.GlobalTheory.SiegelNormalForm.quad Y c z =
      Real.pi * (z ⬝ᵥ Y *ᵥ w) + _root_.GlobalTheory.SiegelNormalForm.quad Y c w := by sorry
