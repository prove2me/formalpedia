-- Prove2me | Theorems.Thm_GlobalTheory_FormalInv_substAlgEquiv_apply
-- name    : GlobalTheory.FormalInv.substAlgEquiv_apply
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:46:43.881117+00:00
-- url     : https://prove2.me/theorems/947d727f-c5b9-44d0-b581-6d6a00064205
-- title:
--   Formal Inv: subst Alg Equiv apply
-- statement:
--   The Formal Inv construction uses the subst Alg Equiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/CoeffSubstInvMemOfTwoLeOrder.lean#L466-L468
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/CoeffSubstInvMemOfTwoLeOrder.lean#L466-L468

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

theorem GlobalTheory.FormalInv.substAlgEquiv_apply (hu : ∀ i, constantCoeff (u i) = 0)
    (hA : IsUnit (linearPart u)) (f : MvPowerSeries σ R) :
    substAlgEquiv hu hA f = f.subst u := by sorry
