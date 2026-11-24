-- Prove2me | Theorems.Thm_GlobalTheory_FormalInv_smul_mem_coeffsIn
-- name    : GlobalTheory.FormalInv.smul_mem_coeffsIn
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T13:34:47.435718+00:00
-- url     : https://prove2.me/theorems/ed4ca5e1-79df-4853-ae74-d464f04caf41
-- title:
--   Formal Inv: smul mem coeffs In
-- statement:
--   The Formal Inv construction uses the smul mem coeffs In property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/CoeffSubstInvMemOfTwoLeOrder.lean#L164-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/CoeffSubstInvMemOfTwoLeOrder.lean#L164-L167

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

theorem GlobalTheory.FormalInv.smul_mem_coeffsIn {κ : Type*} {S : Subring R} {w : κ → σ → ℕ} {g : κ → ℕ}
    {r : R} (hr : r ∈ S) {f : MvPowerSeries σ R} (hf : f ∈ coeffsIn S w g) :
    r • f ∈ coeffsIn S w g := by sorry
