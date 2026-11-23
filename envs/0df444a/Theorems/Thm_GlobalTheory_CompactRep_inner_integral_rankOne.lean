-- Prove2me | Theorems.Thm_GlobalTheory_CompactRep_inner_integral_rankOne
-- name    : GlobalTheory.CompactRep.inner_integral_rankOne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:21:47.722595+00:00
-- url     : https://prove2.me/theorems/ec802e4d-df9c-4d93-9826-43c926ccc1e1
-- title:
--   Compact Rep: inner integral rank One
-- statement:
--   The Compact Rep construction uses the inner integral rank One property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/CompactUnitaryFiniteInvariantSubspace.lean#L40-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/CompactUnitaryFiniteInvariantSubspace.lean#L40-L46

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

theorem GlobalTheory.CompactRep.inner_integral_rankOne {w : X → H} (hFi : Integrable (fun k => rankOne ℂ (w k) (w k)) μ)
    (x y : H) : ⟪y, (∫ k, rankOne ℂ (w k) (w k) ∂μ : H →L[ℂ] H) x⟫_ℂ =
      ∫ k, ⟪w k, x⟫_ℂ * ⟪y, w k⟫_ℂ ∂μ := by sorry
