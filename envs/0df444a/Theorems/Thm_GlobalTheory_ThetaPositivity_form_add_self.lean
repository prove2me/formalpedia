-- Prove2me | Theorems.Thm_GlobalTheory_ThetaPositivity_form_add_self
-- name    : GlobalTheory.ThetaPositivity.form_add_self
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:59:11.495888+00:00
-- url     : https://prove2.me/theorems/02abf709-eb4a-4017-960a-42f204731283
-- title:
--   Theta Positivity: form add self
-- statement:
--   The Theta Positivity construction uses the form add self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ReFormPosOfThetaNeZero.lean#L21-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ReFormPosOfThetaNeZero.lean#L21-L28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ReFormPosOfThetaNeZero
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
open GlobalTheory GlobalTheory.ThetaPositivity
variable {g : ℕ}
open Complex Matrix Filter Topology
open scoped BigOperators Real
variable {g : ℕ}

theorem GlobalTheory.ThetaPositivity.form_add_self {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (z w : Fin g → ℂ) :
    ((z + w) ⬝ᵥ Hm.mulVec (star (z + w))).re =
      (z ⬝ᵥ Hm.mulVec (star z)).re + 2 * (z ⬝ᵥ Hm.mulVec (star w)).re
        + (w ⬝ᵥ Hm.mulVec (star w)).re := by sorry
