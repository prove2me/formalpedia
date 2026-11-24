-- Prove2me | Theorems.Thm_GlobalTheory_FormalCalc_eq_sum_of_additive_param
-- name    : GlobalTheory.FormalCalc.eq_sum_of_additive_param
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T13:33:44.015918+00:00
-- url     : https://prove2.me/theorems/11678367-5eaf-45d1-8c86-cf584e2824cc
-- title:
--   Formal Calc: eq sum of additive param
-- statement:
--   The Formal Calc construction uses the eq sum of additive param property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FormalLogEqSumOfMultiplicativeParam.lean#L121-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FormalLogEqSumOfMultiplicativeParam.lean#L121-L150

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
variable [IsAddTorsionFree A]

theorem GlobalTheory.FormalCalc.eq_sum_of_additive_param [Fintype σ] [Finite τ] {f : MvPowerSeries (σ ⊕ τ) A}
    (h : subst (Sum.elim (fun i => X (inl i) + X (inr (inl i))) fun j => X (inr (inr j)) :
        σ ⊕ τ → MvPowerSeries (σ ⊕ σ ⊕ τ) A) f =
      subst (Sum.elim (fun i => X (inl i)) fun j => X (inr (inr j)) :
        σ ⊕ τ → MvPowerSeries (σ ⊕ σ ⊕ τ) A) f +
      subst (Sum.elim (fun i => X (inr (inl i))) fun j => X (inr (inr j)) :
        σ ⊕ τ → MvPowerSeries (σ ⊕ σ ⊕ τ) A) f) :
    f = ∑ i, X (inl i) * subst (fun j => X (inr j) : τ → MvPowerSeries (σ ⊕ τ) A)
      (subst (Sum.elim (fun _ => 0) X : σ ⊕ τ → MvPowerSeries τ A) (pderiv A (inl i) f)) := by sorry
