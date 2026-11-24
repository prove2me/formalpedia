-- Prove2me | Theorems.Thm_GlobalTheory_FormalInv_rename_mem_weightGe
-- name    : GlobalTheory.FormalInv.rename_mem_weightGe
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T13:34:56.276725+00:00
-- url     : https://prove2.me/theorems/1d1a2006-1bc8-4477-8e7e-b1ecc5a0e83e
-- title:
--   Formal Inv: rename mem weight Ge
-- statement:
--   The Formal Inv construction uses the rename mem weight Ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/CoeffSubstInvMemOfTwoLeOrder.lean#L580-L583
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/CoeffSubstInvMemOfTwoLeOrder.lean#L580-L583

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

theorem GlobalTheory.FormalInv.rename_mem_weightGe [Finite σ] (e : σ → τ) {w : τ → ℕ} {m : ℕ} {f : MvPowerSeries σ R}
    (hf : f ∈ weightGe (w ∘ e) m) : rename e f ∈ weightGe w m := by sorry
