-- Prove2me | Theorems.Thm_GlobalTheory_FormalInv_X_mem_weightGe
-- name    : GlobalTheory.FormalInv.X_mem_weightGe
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:50:24.668672+00:00
-- url     : https://prove2.me/theorems/135d8422-9058-42d8-b548-330b6e1b28d9
-- title:
--   Formal Inv: X mem weight Ge
-- statement:
--   The Formal Inv construction uses the X mem weight Ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/CoeffSubstInvMemOfTwoLeOrder.lean#L573-L578
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/CoeffSubstInvMemOfTwoLeOrder.lean#L573-L578

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_CoeffSubstInvMemOfTwoLeOrder
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries Finsupp
noncomputable section
open GlobalTheory GlobalTheory.FormalInv
variable {σ τ υ ι : Type*} {R : Type*} [CommRing R]
variable {σ' τ' : Type*}

theorem GlobalTheory.FormalInv.X_mem_weightGe (w : σ → ℕ) (s : σ) : (X s : MvPowerSeries σ R) ∈ weightGe w (w s) := by sorry
