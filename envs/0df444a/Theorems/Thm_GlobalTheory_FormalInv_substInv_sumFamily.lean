-- Prove2me | Theorems.Thm_GlobalTheory_FormalInv_substInv_sumFamily
-- name    : GlobalTheory.FormalInv.substInv_sumFamily
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:05:25.206432+00:00
-- url     : https://prove2.me/theorems/0bcb3c95-b10b-40a9-bec9-1466a97d8f4e
-- title:
--   Formal Inv: subst Inv sum Family
-- statement:
--   The Formal Inv construction uses the subst Inv sum Family property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/CoeffSubstInvMemOfTwoLeOrder.lean#L654-L666
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/CoeffSubstInvMemOfTwoLeOrder.lean#L654-L666

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

theorem GlobalTheory.FormalInv.substInv_sumFamily [Fintype σ] [Fintype σ'] [DecidableEq σ] [DecidableEq σ']
    {a : σ → MvPowerSeries σ R} {a' : σ' → MvPowerSeries σ' R}
    (ha : ∀ i, constantCoeff (a i) = 0) (ha' : ∀ j, constantCoeff (a' j) = 0)
    (hA : IsUnit (linearPart a)) (hA' : IsUnit (linearPart a')) :
    IsUnit (linearPart (sumFamily a a')) ∧
      substInv (sumFamily a a') = sumFamily (substInv a) (substInv a') := by sorry
