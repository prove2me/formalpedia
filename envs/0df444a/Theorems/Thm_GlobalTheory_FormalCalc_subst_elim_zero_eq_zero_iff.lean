-- Prove2me | Theorems.Thm_GlobalTheory_FormalCalc_subst_elim_zero_eq_zero_iff
-- name    : GlobalTheory.FormalCalc.subst_elim_zero_eq_zero_iff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T13:33:52.060005+00:00
-- url     : https://prove2.me/theorems/fc9fe5ea-9378-4b63-9a06-0359581b9f17
-- title:
--   Formal Calc: subst elim zero eq zero iff
-- statement:
--   The Formal Calc construction uses the subst elim zero eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FormalLogEqSumOfMultiplicativeParam.lean#L81-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FormalLogEqSumOfMultiplicativeParam.lean#L81-L104

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

theorem GlobalTheory.FormalCalc.subst_elim_zero_eq_zero_iff [Finite σ] [Finite τ] (f : MvPowerSeries (σ ⊕ τ) A) :
    subst (Sum.elim (fun _ => 0) X : σ ⊕ τ → MvPowerSeries τ A) f = 0 ↔
      ∀ α : σ ⊕ τ →₀ ℕ, (∀ i, α (inl i) = 0) → coeff α f = 0 := by sorry
