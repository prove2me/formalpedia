-- Prove2me | Theorems.Thm_GlobalTheory_FormalInv_subst_sumFamily_rename_inl
-- name    : GlobalTheory.FormalInv.subst_sumFamily_rename_inl
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T13:34:53.834548+00:00
-- url     : https://prove2.me/theorems/3f339618-7d31-43e6-a499-75e1944def45
-- title:
--   Formal Inv: subst sum Family rename inl
-- statement:
--   The Formal Inv construction uses the subst sum Family rename inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/CoeffSubstInvMemOfTwoLeOrder.lean#L616-L626
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/CoeffSubstInvMemOfTwoLeOrder.lean#L616-L626

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

theorem GlobalTheory.FormalInv.subst_sumFamily_rename_inl [Finite σ] [Finite σ'] [Finite τ] [Finite τ']
    {a : σ → MvPowerSeries τ R} {a' : σ' → MvPowerSeries τ' R}
    (ha : ∀ i, constantCoeff (a i) = 0) (ha' : ∀ j, constantCoeff (a' j) = 0)
    (f : MvPowerSeries σ R) :
    (rename Sum.inl f).subst (sumFamily a a') = rename Sum.inl (f.subst a) := by sorry
