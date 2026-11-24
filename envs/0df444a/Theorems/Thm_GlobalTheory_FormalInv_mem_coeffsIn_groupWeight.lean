-- Prove2me | Theorems.Thm_GlobalTheory_FormalInv_mem_coeffsIn_groupWeight
-- name    : GlobalTheory.FormalInv.mem_coeffsIn_groupWeight
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T13:34:37.64526+00:00
-- url     : https://prove2.me/theorems/1ac976d3-2621-4146-a070-0b9ef7fe4e17
-- title:
--   Formal Inv: mem coeffs In group Weight
-- statement:
--   The Formal Inv construction uses the mem coeffs In group Weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/CoeffSubstInvMemOfTwoLeOrder.lean#L543-L571
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/CoeffSubstInvMemOfTwoLeOrder.lean#L543-L571

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

theorem GlobalTheory.FormalInv.mem_coeffsIn_groupWeight [Finite σ] [Finite σ'] {S : Subring R} {g g' : ℕ}
    {f : MvPowerSeries (σ ⊕ σ') R} :
    f ∈ coeffsIn S (groupWeight σ σ') (fun b => bif b then g else g') ↔
      ∀ (α : σ →₀ ℕ) (β : σ' →₀ ℕ), α.degree < g → β.degree < g' →
        coeff (α.sumElim β) f ∈ S := by sorry
