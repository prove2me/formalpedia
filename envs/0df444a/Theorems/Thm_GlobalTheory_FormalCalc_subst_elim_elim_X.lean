-- Prove2me | Theorems.Thm_GlobalTheory_FormalCalc_subst_elim_elim_X
-- name    : GlobalTheory.FormalCalc.subst_elim_elim_X
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:56:21.068278+00:00
-- url     : https://prove2.me/theorems/9fcb5904-c589-47f4-87ee-02b1ff8d5a70
-- title:
--   Formal Calc: subst elim elim X
-- statement:
--   The Formal Calc construction uses the subst elim elim X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FormalLogEqSumOfMultiplicativeParam.lean#L31-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FormalLogEqSumOfMultiplicativeParam.lean#L31-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalExpMulFormalExpNeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalLogEqSumOfMultiplicativeParam
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.FormalCalc
open MvPowerSeries Sum
variable {σ τ ι κ μ A : Type*} [CommRing A]

theorem GlobalTheory.FormalCalc.subst_elim_elim_X (f : MvPowerSeries (σ ⊕ τ ⊕ ι) A) :
    subst (Sum.elim (fun i => X (inl i)) (Sum.elim (fun j => X (inr (inl j)))
      fun j => X (inr (inr j))) : σ ⊕ τ ⊕ ι → MvPowerSeries (σ ⊕ τ ⊕ ι) A) f = f := by sorry
