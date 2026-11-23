-- Prove2me | Theorems.Thm_GlobalTheory_FormalCalc_subst_sumElim
-- name    : GlobalTheory.FormalCalc.subst_sumElim
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:51:19.073856+00:00
-- url     : https://prove2.me/theorems/fc7f386b-266d-42f4-9590-054f82b3474c
-- title:
--   Formal Calc: subst sum Elim
-- statement:
--   The Formal Calc construction uses the subst sum Elim property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FormalLogEqSumOfMultiplicativeParam.lean#L18-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FormalLogEqSumOfMultiplicativeParam.lean#L18-L22

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

theorem GlobalTheory.FormalCalc.subst_sumElim (b : κ → MvPowerSeries μ A) (u : σ → MvPowerSeries κ A)
    (t : τ → MvPowerSeries κ A) :
    (fun i => subst b (Sum.elim u t i)) =
      Sum.elim (fun i => subst b (u i)) fun j => subst b (t j) := by sorry
