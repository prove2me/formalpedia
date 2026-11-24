-- Prove2me | Theorems.Thm_GlobalTheory_FormalInv_two_le_order_substInv_sub_X
-- name    : GlobalTheory.FormalInv.two_le_order_substInv_sub_X
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T13:34:42.896803+00:00
-- url     : https://prove2.me/theorems/287cd1aa-1c7a-481a-9d44-31834c0763f7
-- title:
--   Formal Inv: two le order subst Inv sub X
-- statement:
--   The Formal Inv construction uses the two le order subst Inv sub X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/CoeffSubstInvMemOfTwoLeOrder.lean#L501-L505
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/CoeffSubstInvMemOfTwoLeOrder.lean#L501-L505

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

theorem GlobalTheory.FormalInv.two_le_order_substInv_sub_X (hu : ∀ i, (2 : ℕ∞) ≤ (u i - X i).order) (i : σ) :
    (2 : ℕ∞) ≤ (substInv u i - X i).order := by sorry
