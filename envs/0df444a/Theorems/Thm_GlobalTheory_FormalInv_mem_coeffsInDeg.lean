-- Prove2me | Theorems.Thm_GlobalTheory_FormalInv_mem_coeffsInDeg
-- name    : GlobalTheory.FormalInv.mem_coeffsInDeg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:50:27.238489+00:00
-- url     : https://prove2.me/theorems/9e06afdf-50a0-4df6-bcf8-bff1f50fb38b
-- title:
--   Formal Inv: mem coeffs In Deg
-- statement:
--   The Formal Inv construction uses the mem coeffs In Deg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/CoeffSubstInvMemOfTwoLeOrder.lean#L191-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/CoeffSubstInvMemOfTwoLeOrder.lean#L191-L193

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

theorem GlobalTheory.FormalInv.mem_coeffsInDeg {S : Subring R} {g : ℕ} {f : MvPowerSeries σ R} :
    f ∈ coeffsInDeg σ S g ↔ ∀ d : σ →₀ ℕ, d.degree < g → coeff d f ∈ S := by sorry
