-- Prove2me | Theorems.Thm_GlobalTheory_FormalInv_subst_sumFamily_sumFamily
-- name    : GlobalTheory.FormalInv.subst_sumFamily_sumFamily
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:34:25.177737+00:00
-- url     : https://prove2.me/theorems/dbe59e19-7a82-4f32-90a5-ec4dd6260a62
-- title:
--   Formal Inv: subst sum Family sum Family
-- statement:
--   The Formal Inv construction uses the subst sum Family sum Family property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/CoeffSubstInvMemOfTwoLeOrder.lean#L640-L648
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/CoeffSubstInvMemOfTwoLeOrder.lean#L640-L648

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

theorem GlobalTheory.FormalInv.subst_sumFamily_sumFamily {υ' : Type*} [Finite σ] [Finite σ'] [Finite τ] [Finite τ']
    (b : υ → MvPowerSeries σ R) (b' : υ' → MvPowerSeries σ' R)
    {a : σ → MvPowerSeries τ R} {a' : σ' → MvPowerSeries τ' R}
    (ha : ∀ i, constantCoeff (a i) = 0) (ha' : ∀ j, constantCoeff (a' j) = 0) (s : υ ⊕ υ') :
    (sumFamily b b' s).subst (sumFamily a a') =
      sumFamily (fun i => (b i).subst a) (fun j => (b' j).subst a') s := by sorry
