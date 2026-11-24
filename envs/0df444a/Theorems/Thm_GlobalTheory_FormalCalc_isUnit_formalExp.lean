-- Prove2me | Theorems.Thm_GlobalTheory_FormalCalc_isUnit_formalExp
-- name    : GlobalTheory.FormalCalc.isUnit_formalExp
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T13:34:01.912779+00:00
-- url     : https://prove2.me/theorems/619980a6-c8b8-46f4-be81-0febb615a455
-- title:
--   Formal Calc: is Unit formal Exp
-- statement:
--   The Formal Calc construction uses the is Unit formal Exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FormalExpMulFormalExpNeg.lean#L32-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FormalExpMulFormalExpNeg.lean#L32-L34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalExpMulFormalExpNeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.FormalCalc
open MvPowerSeries
variable {σ τ A B : Type*} [CommRing A] [Algebra ℚ A] [CommRing B] [Algebra ℚ B]

theorem GlobalTheory.FormalCalc.isUnit_formalExp {f : MvPowerSeries σ A} (hf : constantCoeff f = 0) :
    IsUnit (formalExp f) := by sorry
