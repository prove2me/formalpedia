-- Prove2me | Theorems.Thm_GlobalTheory_SiegelNormalForm_form_single
-- name    : GlobalTheory.SiegelNormalForm.form_single
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:57:45.050748+00:00
-- url     : https://prove2.me/theorems/de9c66c7-9dde-4343-a389-3868d59c2347
-- title:
--   Siegel Normal Form: form single
-- statement:
--   The Siegel Normal Form construction uses the form single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/IsUnitOfLagrangian.lean#L25-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/IsUnitOfLagrangian.lean#L25-L28

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

theorem GlobalTheory.SiegelNormalForm.form_single (Y : Matrix (Fin g) (Fin g) ℂ)
    (i j : Fin g) :
    (Pi.single i 1 : Fin g → ℂ) ⬝ᵥ Y *ᵥ star (Pi.single j 1 : Fin g → ℂ) = Y i j := by sorry
