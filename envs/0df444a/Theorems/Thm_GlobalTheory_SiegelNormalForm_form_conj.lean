-- Prove2me | Theorems.Thm_GlobalTheory_SiegelNormalForm_form_conj
-- name    : GlobalTheory.SiegelNormalForm.form_conj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:57:51.170847+00:00
-- url     : https://prove2.me/theorems/563264e8-0006-4b74-80b0-80e0297dd40a
-- title:
--   Siegel Normal Form: form conj
-- statement:
--   The Siegel Normal Form construction uses the form conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/IsUnitOfLagrangian.lean#L33-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/IsUnitOfLagrangian.lean#L33-L36

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

theorem GlobalTheory.SiegelNormalForm.form_conj {Hm : Matrix (Fin g) (Fin g) ℂ}
    (hH : Hm.IsHermitian) (z w : Fin g → ℂ) :
    star (z ⬝ᵥ Hm *ᵥ star w) = w ⬝ᵥ Hm *ᵥ star z := by sorry
