-- Prove2me | Theorems.Thm_GlobalTheory_FormalCalc_subst_subst
-- name    : GlobalTheory.FormalCalc.subst_subst
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:52:00.984789+00:00
-- url     : https://prove2.me/theorems/7ec0eea8-0cb6-499a-a006-6e76911ac269
-- title:
--   Formal Calc: subst subst
-- statement:
--   The Formal Calc construction uses the subst subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FormalLogEqSumOfMultiplicativeParam.lean#L13-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FormalLogEqSumOfMultiplicativeParam.lean#L13-L16

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

theorem GlobalTheory.FormalCalc.subst_subst [Finite ι] {a : ι → MvPowerSeries κ A} {b : κ → MvPowerSeries μ A}
    (hb : HasSubst b) (ha : ∀ i, constantCoeff (a i) = 0) (f : MvPowerSeries ι A) :
    subst b (subst a f) = subst (fun i => subst b (a i)) f := by sorry
