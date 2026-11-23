-- Prove2me | Theorems.Thm_GlobalTheory_FormalCalc_pderiv_X_ite
-- name    : GlobalTheory.FormalCalc.pderiv_X_ite
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:52:16.236322+00:00
-- url     : https://prove2.me/theorems/81bd6d06-85f5-44dc-9e07-0c72b5c3013f
-- title:
--   Formal Calc: pderiv X ite
-- statement:
--   The Formal Calc construction uses the pderiv X ite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FormalLogEqSumOfMultiplicativeParam.lean#L44-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FormalLogEqSumOfMultiplicativeParam.lean#L44-L48

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

theorem GlobalTheory.FormalCalc.pderiv_X_ite [DecidableEq κ] (i j : κ) :
    pderiv A i (X j : MvPowerSeries κ A) = if j = i then 1 else 0 := by sorry
