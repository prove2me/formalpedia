-- Prove2me | Theorems.Thm_GlobalTheory_SiegelNormalForm_isUnit_of_lagrangian
-- name    : GlobalTheory.SiegelNormalForm.isUnit_of_lagrangian
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:57:55.740436+00:00
-- url     : https://prove2.me/theorems/7bd87bbf-f5cc-4fab-a33d-73dd96b9d4fd
-- title:
--   Siegel Normal Form: is Unit of lagrangian
-- statement:
--   The Siegel Normal Form construction uses the is Unit of lagrangian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/IsUnitOfLagrangian.lean#L42-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/IsUnitOfLagrangian.lean#L42-L89

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

theorem GlobalTheory.SiegelNormalForm.isUnit_of_lagrangian (P Hm : Matrix (Fin g) (Fin g) ℂ)
    (f : Fin g → Fin g → ℂ)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm *ᵥ (star z)).re)
    (Y : Matrix (Fin g) (Fin g) ℝ) (hY : Pᵀ * Hm * P.map star = Y.map (↑))
    (hf : ∀ i j, ((P *ᵥ Pi.single i 1) ⬝ᵥ Hm *ᵥ star (f j)).im = if i = j then -1 else 0) :
    IsUnit P := by sorry
