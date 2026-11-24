-- Prove2me | Theorems.Thm_GlobalTheory_FormalInv_subst_sumFamily_rename_inr
-- name    : GlobalTheory.FormalInv.subst_sumFamily_rename_inr
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:34:25.403669+00:00
-- url     : https://prove2.me/theorems/874c83fb-c6e8-44d7-95ab-a6fd00e7f1ad
-- title:
--   Formal Inv: subst sum Family rename inr
-- statement:
--   The Formal Inv construction uses the subst sum Family rename inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/CoeffSubstInvMemOfTwoLeOrder.lean#L628-L638
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/CoeffSubstInvMemOfTwoLeOrder.lean#L628-L638

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

theorem GlobalTheory.FormalInv.subst_sumFamily_rename_inr [Finite σ] [Finite σ'] [Finite τ] [Finite τ']
    {a : σ → MvPowerSeries τ R} {a' : σ' → MvPowerSeries τ' R}
    (ha : ∀ i, constantCoeff (a i) = 0) (ha' : ∀ j, constantCoeff (a' j) = 0)
    (f : MvPowerSeries σ' R) :
    (rename Sum.inr f).subst (sumFamily a a') = rename Sum.inr (f.subst a') := by sorry
