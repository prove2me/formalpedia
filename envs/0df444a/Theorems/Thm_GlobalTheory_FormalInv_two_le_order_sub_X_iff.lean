-- Prove2me | Theorems.Thm_GlobalTheory_FormalInv_two_le_order_sub_X_iff
-- name    : GlobalTheory.FormalInv.two_le_order_sub_X_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:47:53.813777+00:00
-- url     : https://prove2.me/theorems/dea7f0cf-df0f-41fd-916b-cd05fc43cdb8
-- title:
--   Formal Inv: two le order sub X iff
-- statement:
--   The Formal Inv construction uses the two le order sub X iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/CoeffSubstInvMemOfTwoLeOrder.lean#L491-L499
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/CoeffSubstInvMemOfTwoLeOrder.lean#L491-L499

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
variable [Fintype σ] [DecidableEq σ]
variable {u v : σ → MvPowerSeries σ R}
omit [Fintype σ]

theorem GlobalTheory.FormalInv.two_le_order_sub_X_iff :
    (∀ i, (2 : ℕ∞) ≤ (u i - X i).order) ↔
      (∀ i, constantCoeff (u i) = 0) ∧ linearPart u = 1 := by sorry
