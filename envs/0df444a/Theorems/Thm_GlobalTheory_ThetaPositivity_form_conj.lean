-- Prove2me | Theorems.Thm_GlobalTheory_ThetaPositivity_form_conj
-- name    : GlobalTheory.ThetaPositivity.form_conj
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T21:06:10.407697+00:00
-- url     : https://prove2.me/theorems/2dc02567-224b-4f13-b554-f9c88a097ef9
-- title:
--   Theta Positivity: form conj
-- statement:
--   The Theta Positivity construction uses the form conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ReFormPosOfThetaNeZero.lean#L14-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ReFormPosOfThetaNeZero.lean#L14-L16

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

theorem GlobalTheory.ThetaPositivity.form_conj {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (z w : Fin g → ℂ) :
    w ⬝ᵥ Hm.mulVec (star z) = star (z ⬝ᵥ Hm.mulVec (star w)) := by sorry
