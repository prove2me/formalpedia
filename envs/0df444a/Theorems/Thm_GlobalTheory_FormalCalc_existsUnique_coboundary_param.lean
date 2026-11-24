-- Prove2me | Theorems.Thm_GlobalTheory_FormalCalc_existsUnique_coboundary_param
-- name    : GlobalTheory.FormalCalc.existsUnique_coboundary_param
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T13:33:54.686989+00:00
-- url     : https://prove2.me/theorems/7e1a342b-82db-43a6-9f86-8cc1669d82b0
-- title:
--   Formal Calc: exists Unique coboundary param
-- statement:
--   The Formal Calc construction uses the exists Unique coboundary param property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FormalLogEqSumOfMultiplicativeParam.lean#L158-L266
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FormalLogEqSumOfMultiplicativeParam.lean#L158-L266

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
variable [Algebra ℚ A]

theorem GlobalTheory.FormalCalc.existsUnique_coboundary_param [Finite σ] [Finite τ] {B : MvPowerSeries (σ ⊕ σ ⊕ τ) A}
    (h0 : subst (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) X) :
        σ ⊕ σ ⊕ τ → MvPowerSeries τ A) B = 0)
    (hsymm : subst (Sum.elim (fun i => X (inr (inl i))) (Sum.elim (fun i => X (inl i)) fun j => X (inr (inr j))) :
        σ ⊕ σ ⊕ τ → MvPowerSeries (σ ⊕ σ ⊕ τ) A) B = B)
    (hcoc : subst (Sum.elim (fun i => X (inl i))
        (Sum.elim (fun i => X (inr (inl i))) fun j => X (inr (inr (inr j)))) :
        σ ⊕ σ ⊕ τ → MvPowerSeries (σ ⊕ σ ⊕ σ ⊕ τ) A) B +
      subst (Sum.elim (fun i => X (inl i) + X (inr (inl i)))
        (Sum.elim (fun i => X (inr (inr (inl i)))) fun j => X (inr (inr (inr j)))) :
        σ ⊕ σ ⊕ τ → MvPowerSeries (σ ⊕ σ ⊕ σ ⊕ τ) A) B =
      subst (Sum.elim (fun i => X (inr (inl i)))
        (Sum.elim (fun i => X (inr (inr (inl i)))) fun j => X (inr (inr (inr j)))) :
        σ ⊕ σ ⊕ τ → MvPowerSeries (σ ⊕ σ ⊕ σ ⊕ τ) A) B +
      subst (Sum.elim (fun i => X (inl i))
        (Sum.elim (fun i => X (inr (inl i)) + X (inr (inr (inl i)))) fun j => X (inr (inr (inr j)))) :
        σ ⊕ σ ⊕ τ → MvPowerSeries (σ ⊕ σ ⊕ σ ⊕ τ) A) B) :
    ∃! k : MvPowerSeries (σ ⊕ τ) A, subst (Sum.elim (fun _ => 0) X : σ ⊕ τ → MvPowerSeries τ A) k = 0 ∧
      (∀ i, subst (Sum.elim (fun _ => 0) X : σ ⊕ τ → MvPowerSeries τ A) (pderiv A (inl i) k) = 0) ∧
      B = subst (Sum.elim (fun i => X (inl i) + X (inr (inl i))) fun j => X (inr (inr j)) :
        σ ⊕ τ → MvPowerSeries (σ ⊕ σ ⊕ τ) A) k -
      subst (Sum.elim (fun i => X (inl i)) fun j => X (inr (inr j)) :
        σ ⊕ τ → MvPowerSeries (σ ⊕ σ ⊕ τ) A) k -
      subst (Sum.elim (fun i => X (inr (inl i))) fun j => X (inr (inr j)) :
        σ ⊕ τ → MvPowerSeries (σ ⊕ σ ⊕ τ) A) k := by sorry
