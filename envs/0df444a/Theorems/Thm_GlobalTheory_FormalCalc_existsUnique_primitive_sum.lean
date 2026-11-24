-- Prove2me | Theorems.Thm_GlobalTheory_FormalCalc_existsUnique_primitive_sum
-- name    : GlobalTheory.FormalCalc.existsUnique_primitive_sum
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T13:34:00.137296+00:00
-- url     : https://prove2.me/theorems/7ea9cec7-eba8-4dd2-a66b-d63c3186c95d
-- title:
--   Formal Calc: exists Unique primitive sum
-- statement:
--   The Formal Calc construction uses the exists Unique primitive sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FormalLogEqSumOfMultiplicativeParam.lean#L106-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FormalLogEqSumOfMultiplicativeParam.lean#L106-L113

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

theorem GlobalTheory.FormalCalc.existsUnique_primitive_sum [Finite σ] [Finite τ] [Algebra ℚ A]
    (a : σ → MvPowerSeries (σ ⊕ τ) A)
    (ha : ∀ i j, pderiv A (inl i) (a j) = pderiv A (inl j) (a i)) :
    ∃! f : MvPowerSeries (σ ⊕ τ) A,
      subst (Sum.elim (fun _ => 0) X : σ ⊕ τ → MvPowerSeries τ A) f = 0 ∧
        ∀ i, pderiv A (inl i) f = a i := by sorry
