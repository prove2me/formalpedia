-- Prove2me | Theorems.Thm_GlobalTheory_FormalInv_higherPart_mem_coeffsInDeg
-- name    : GlobalTheory.FormalInv.higherPart_mem_coeffsInDeg
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T13:34:47.121106+00:00
-- url     : https://prove2.me/theorems/0c3ecdac-f3bf-4b56-93e9-e490dea9a328
-- title:
--   Formal Inv: higher Part mem coeffs In Deg
-- statement:
--   The Formal Inv construction uses the higher Part mem coeffs In Deg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/CoeffSubstInvMemOfTwoLeOrder.lean#L360-L369
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/CoeffSubstInvMemOfTwoLeOrder.lean#L360-L369

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

theorem GlobalTheory.FormalInv.higherPart_mem_coeffsInDeg [Fintype σ] {u : ι → MvPowerSeries σ R} {i : ι}
    (hu : constantCoeff (u i) = 0) {S : Subring R} {g : ℕ} (huS : u i ∈ coeffsInDeg σ S g) :
    higherPart u i ∈ coeffsInDeg σ S g := by sorry
