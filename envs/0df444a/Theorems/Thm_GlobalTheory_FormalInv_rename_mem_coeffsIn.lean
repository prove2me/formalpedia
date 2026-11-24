-- Prove2me | Theorems.Thm_GlobalTheory_FormalInv_rename_mem_coeffsIn
-- name    : GlobalTheory.FormalInv.rename_mem_coeffsIn
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T13:34:40.583743+00:00
-- url     : https://prove2.me/theorems/c5a790d3-c431-4a3f-8ec7-f8eabbf2b2cb
-- title:
--   Formal Inv: rename mem coeffs In
-- statement:
--   The Formal Inv construction uses the rename mem coeffs In property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/CoeffSubstInvMemOfTwoLeOrder.lean#L585-L590
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/CoeffSubstInvMemOfTwoLeOrder.lean#L585-L590

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

theorem GlobalTheory.FormalInv.rename_mem_coeffsIn {κ : Type*} [Finite σ] (e : σ → τ) {S : Subring R} {w : κ → τ → ℕ}
    {g : κ → ℕ} {f : MvPowerSeries σ R} (hf : f ∈ coeffsIn S (fun k => w k ∘ e) g) :
    rename e f ∈ coeffsIn S w g := by sorry
