-- Prove2me | Theorems.Thm_GlobalTheory_FormalInv_coeff_substInv_mem_of_two_le_order
-- name    : GlobalTheory.FormalInv.coeff_substInv_mem_of_two_le_order
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T13:34:33.09935+00:00
-- url     : https://prove2.me/theorems/641c2302-b223-4f41-b066-582a21ffabcb
-- title:
--   Formal Inv: coeff subst Inv mem of two le order
-- statement:
--   The Formal Inv construction uses the coeff subst Inv mem of two le order property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/CoeffSubstInvMemOfTwoLeOrder.lean#L507-L513
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/CoeffSubstInvMemOfTwoLeOrder.lean#L507-L513

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

theorem GlobalTheory.FormalInv.coeff_substInv_mem_of_two_le_order (hu : ∀ i, (2 : ℕ∞) ≤ (u i - X i).order)
    {S : Subring R} {g : ℕ} (huS : ∀ i (d : σ →₀ ℕ), d.degree < g → coeff d (u i) ∈ S) (i : σ)
    (d : σ →₀ ℕ) (hd : d.degree < g) : coeff d (substInv u i) ∈ S := by sorry
