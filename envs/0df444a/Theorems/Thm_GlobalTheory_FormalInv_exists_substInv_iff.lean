-- Prove2me | Theorems.Thm_GlobalTheory_FormalInv_exists_substInv_iff
-- name    : GlobalTheory.FormalInv.exists_substInv_iff
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T13:34:26.977933+00:00
-- url     : https://prove2.me/theorems/5f264c04-294b-4647-8cdf-7bee939f8f96
-- title:
--   Formal Inv: exists subst Inv iff
-- statement:
--   The Formal Inv construction uses the exists subst Inv iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/CoeffSubstInvMemOfTwoLeOrder.lean#L440-L445
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/CoeffSubstInvMemOfTwoLeOrder.lean#L440-L445

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

theorem GlobalTheory.FormalInv.exists_substInv_iff (hu : ∀ i, constantCoeff (u i) = 0) :
    (∃ v : σ → MvPowerSeries σ R, (∀ i, constantCoeff (v i) = 0) ∧
      (∀ i, (u i).subst v = X i) ∧ ∀ i, (v i).subst u = X i) ↔ IsUnit (linearPart u) := by sorry
