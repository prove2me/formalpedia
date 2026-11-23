-- Prove2me | Theorems.Thm_GlobalTheory_FormalInv_substAlgEquiv_symm_apply
-- name    : GlobalTheory.FormalInv.substAlgEquiv_symm_apply
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:46:45.837314+00:00
-- url     : https://prove2.me/theorems/e553e257-deb6-4781-b2a2-5288ec876f6b
-- title:
--   Formal Inv: subst Alg Equiv symm apply
-- statement:
--   The Formal Inv construction uses the subst Alg Equiv symm apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/CoeffSubstInvMemOfTwoLeOrder.lean#L470-L472
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/CoeffSubstInvMemOfTwoLeOrder.lean#L470-L472

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

theorem GlobalTheory.FormalInv.substAlgEquiv_symm_apply (hu : ∀ i, constantCoeff (u i) = 0)
    (hA : IsUnit (linearPart u)) (f : MvPowerSeries σ R) :
    (substAlgEquiv hu hA).symm f = f.subst (substInv u) := by sorry
