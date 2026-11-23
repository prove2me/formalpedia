-- Prove2me | Theorems.Thm_GlobalTheory_FormalCalc_coeff_subst_kill
-- name    : GlobalTheory.FormalCalc.coeff_subst_kill
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:56:41.456006+00:00
-- url     : https://prove2.me/theorems/d2898651-21a9-44b4-9e00-048b63473307
-- title:
--   Formal Calc: coeff subst kill
-- statement:
--   The Formal Calc construction uses the coeff subst kill property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FormalLogEqSumOfMultiplicativeParam.lean#L52-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FormalLogEqSumOfMultiplicativeParam.lean#L52-L71

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
open Classical

theorem GlobalTheory.FormalCalc.coeff_subst_kill (e : ι → κ) {b : κ → MvPowerSeries κ A} (hb0 : ∀ i, b (e i) = 0)
    (hb1 : ∀ k, k ∉ Set.range e → b k = X k) (f : MvPowerSeries κ A) (α : κ →₀ ℕ) :
    coeff α (subst b f) = if ∀ i, α (e i) = 0 then coeff α f else 0 := by sorry
