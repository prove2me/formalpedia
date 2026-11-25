-- Prove2me | Theorems.Thm_GlobalTheory_FormalCalc_formalExp_mul_formalExp_neg
-- name    : GlobalTheory.FormalCalc.formalExp_mul_formalExp_neg
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:33:13.072449+00:00
-- url     : https://prove2.me/theorems/d019953b-a701-4386-895a-2883998ddf44
-- title:
--   Formal Calc: formal Exp mul formal Exp neg
-- statement:
--   The Formal Calc construction uses the formal Exp mul formal Exp neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FormalExpMulFormalExpNeg.lean#L96-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FormalExpMulFormalExpNeg.lean#L96-L98

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

theorem GlobalTheory.FormalCalc.formalExp_mul_formalExp_neg {f : MvPowerSeries σ A} (hf : constantCoeff f = 0) :
    formalExp f * formalExp (-f) = 1 := by sorry
