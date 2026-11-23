-- Prove2me | Theorems.Thm_GlobalTheory_FormalInv_mem_coeffsIn
-- name    : GlobalTheory.FormalInv.mem_coeffsIn
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:50:30.687067+00:00
-- url     : https://prove2.me/theorems/1c022c00-574a-4fb2-8041-6d504e33caa2
-- title:
--   Formal Inv: mem coeffs In
-- statement:
--   The Formal Inv construction uses the mem coeffs In property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/CoeffSubstInvMemOfTwoLeOrder.lean#L160-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/CoeffSubstInvMemOfTwoLeOrder.lean#L160-L162

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

theorem GlobalTheory.FormalInv.mem_coeffsIn {κ : Type*} {S : Subring R} {w : κ → σ → ℕ} {g : κ → ℕ}
    {f : MvPowerSeries σ R} :
    f ∈ coeffsIn S w g ↔ ∀ d, (∀ k, weight (w k) d < g k) → coeff d f ∈ S := by sorry
