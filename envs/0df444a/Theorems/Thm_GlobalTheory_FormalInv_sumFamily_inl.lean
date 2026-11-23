-- Prove2me | Theorems.Thm_GlobalTheory_FormalInv_sumFamily_inl
-- name    : GlobalTheory.FormalInv.sumFamily_inl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:46:45.612796+00:00
-- url     : https://prove2.me/theorems/7105c260-dca8-4129-b487-ecc4f928fc0a
-- title:
--   Formal Inv: sum Family inl
-- statement:
--   The Formal Inv construction uses the sum Family inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/CoeffSubstInvMemOfTwoLeOrder.lean#L525-L527
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/CoeffSubstInvMemOfTwoLeOrder.lean#L525-L527

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

theorem GlobalTheory.FormalInv.sumFamily_inl [Finite τ] [Finite τ'] (a : σ → MvPowerSeries τ R)
    (a' : σ' → MvPowerSeries τ' R) (i : σ) :
    sumFamily a a' (Sum.inl i) = rename Sum.inl (a i) := by sorry

attribute [defeq] GlobalTheory.FormalInv.sumFamily_inl
