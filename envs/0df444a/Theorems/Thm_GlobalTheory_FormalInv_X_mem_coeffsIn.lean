-- Prove2me | Theorems.Thm_GlobalTheory_FormalInv_X_mem_coeffsIn
-- name    : GlobalTheory.FormalInv.X_mem_coeffsIn
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:50:12.559559+00:00
-- url     : https://prove2.me/theorems/6f83aee2-fa8b-4bd2-9288-eac4e5fd8f17
-- title:
--   Formal Inv: X mem coeffs In
-- statement:
--   The Formal Inv construction uses the X mem coeffs In property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/CoeffSubstInvMemOfTwoLeOrder.lean#L169-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/CoeffSubstInvMemOfTwoLeOrder.lean#L169-L172

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

theorem GlobalTheory.FormalInv.X_mem_coeffsIn {κ : Type*} {S : Subring R} {w : κ → σ → ℕ} {g : κ → ℕ} (s : σ) :
    (X s : MvPowerSeries σ R) ∈ coeffsIn S w g := by sorry
