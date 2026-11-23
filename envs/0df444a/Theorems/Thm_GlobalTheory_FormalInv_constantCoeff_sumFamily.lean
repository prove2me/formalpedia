-- Prove2me | Theorems.Thm_GlobalTheory_FormalInv_constantCoeff_sumFamily
-- name    : GlobalTheory.FormalInv.constantCoeff_sumFamily
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:47:12.686332+00:00
-- url     : https://prove2.me/theorems/815e60df-7df0-454e-978a-4c82d60b9994
-- title:
--   Formal Inv: constant Coeff sum Family
-- statement:
--   The Formal Inv construction uses the constant Coeff sum Family property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/CoeffSubstInvMemOfTwoLeOrder.lean#L533-L537
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/CoeffSubstInvMemOfTwoLeOrder.lean#L533-L537

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

theorem GlobalTheory.FormalInv.constantCoeff_sumFamily [Finite τ] [Finite τ'] {a : σ → MvPowerSeries τ R}
    {a' : σ' → MvPowerSeries τ' R} (ha : ∀ i, constantCoeff (a i) = 0)
    (ha' : ∀ j, constantCoeff (a' j) = 0) (s : σ ⊕ σ') :
    constantCoeff (sumFamily a a' s) = 0 := by sorry
