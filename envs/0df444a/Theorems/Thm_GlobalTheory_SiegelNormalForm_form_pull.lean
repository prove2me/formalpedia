-- Prove2me | Theorems.Thm_GlobalTheory_SiegelNormalForm_form_pull
-- name    : GlobalTheory.SiegelNormalForm.form_pull
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:31:17.143332+00:00
-- url     : https://prove2.me/theorems/06d239c3-b045-4bb1-882c-86d9e910aeaa
-- title:
--   Siegel Normal Form: form pull
-- statement:
--   The Siegel Normal Form construction uses the form pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/IsUnitOfLagrangian.lean#L15-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/IsUnitOfLagrangian.lean#L15-L20

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

theorem GlobalTheory.SiegelNormalForm.form_pull (P Hm : Matrix (Fin g) (Fin g) ℂ)
    (z w : Fin g → ℂ) :
    (P *ᵥ z) ⬝ᵥ Hm *ᵥ star (P *ᵥ w) = z ⬝ᵥ (Pᵀ * Hm * P.map star) *ᵥ star w := by sorry
