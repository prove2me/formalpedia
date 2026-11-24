-- Prove2me | Theorems.Thm_GlobalTheory_ThetaPositivity_eq_zero_of_neg
-- name    : GlobalTheory.ThetaPositivity.eq_zero_of_neg
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T21:06:09.248749+00:00
-- url     : https://prove2.me/theorems/41848d8f-122d-4921-a605-09755c11fd7c
-- title:
--   Theta Positivity: eq zero of neg
-- statement:
--   The Theta Positivity construction uses the eq zero of neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ReFormPosOfThetaNeZero.lean#L106-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ReFormPosOfThetaNeZero.lean#L106-L148

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

theorem GlobalTheory.ThetaPositivity.eq_zero_of_neg {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian)
    {θ : (Fin g → ℂ) → ℂ} (hθ : Differentiable ℂ θ) {C : ℝ}
    (hC : ∀ z, ‖θ z‖ ≤ C * Real.exp (Real.pi / 2 * (z ⬝ᵥ Hm.mulVec (star z)).re))
    {w : Fin g → ℂ} (hw : (w ⬝ᵥ Hm.mulVec (star w)).re < 0) : θ = 0 := by sorry
