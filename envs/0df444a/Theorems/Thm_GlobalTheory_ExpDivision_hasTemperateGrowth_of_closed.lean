-- Prove2me | Theorems.Thm_GlobalTheory_ExpDivision_hasTemperateGrowth_of_closed
-- name    : GlobalTheory.ExpDivision.hasTemperateGrowth_of_closed
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:43:27.633768+00:00
-- url     : https://prove2.me/theorems/bdf2f10c-71fc-4f98-b90b-0d5cc412b6e2
-- title:
--   Exp Division: has Temperate Growth of closed
-- statement:
--   The Exp Division construction uses the has Temperate Growth of closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IdentityAsSumExpMinusOne.lean#L7-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IdentityAsSumExpMinusOne.lean#L7-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdentityAsSumExpMinusOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open GlobalTheory GlobalTheory.ExpDivision

theorem GlobalTheory.ExpDivision.hasTemperateGrowth_of_closed (S : Set (ℝ → ℂ))
    (hd : ∀ f ∈ S, Differentiable ℝ f) (hc : ∀ f ∈ S, deriv f ∈ S)
    (hb : ∀ f ∈ S, ∃ (k : ℕ) (C : ℝ), ∀ x, ‖f x‖ ≤ C * (1 + ‖x‖) ^ k)
    {f : ℝ → ℂ} (hf : f ∈ S) : f.HasTemperateGrowth := by sorry
