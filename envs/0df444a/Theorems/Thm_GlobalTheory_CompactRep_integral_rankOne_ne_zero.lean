-- Prove2me | Theorems.Thm_GlobalTheory_CompactRep_integral_rankOne_ne_zero
-- name    : GlobalTheory.CompactRep.integral_rankOne_ne_zero
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:16:15.624+00:00
-- url     : https://prove2.me/theorems/6bfea998-1469-4000-99d0-b8d73f96af1f
-- title:
--   Compact Rep: integral rank One ne zero
-- statement:
--   The Compact Rep construction uses the integral rank One ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/CompactUnitaryFiniteInvariantSubspace.lean#L59-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/CompactUnitaryFiniteInvariantSubspace.lean#L59-L74

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_CompactUnitaryFiniteInvariantSubspace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory InnerProductSpace
open scoped InnerProductSpace
open GlobalTheory GlobalTheory.CompactRep
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H] {X : Type} [MeasurableSpace X] {μ : Measure X}

theorem GlobalTheory.CompactRep.integral_rankOne_ne_zero {w : X → H}
    (hFi : Integrable (fun k => rankOne ℂ (w k) (w k)) μ) (v : H)
    (hpos : 0 < ∫ k, ‖⟪v, w k⟫_ℂ‖ ^ 2 ∂μ) :
    (∫ k, rankOne ℂ (w k) (w k) ∂μ : H →L[ℂ] H) ≠ 0 := by sorry
