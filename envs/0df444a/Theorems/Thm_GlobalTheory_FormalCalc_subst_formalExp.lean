-- Prove2me | Theorems.Thm_GlobalTheory_FormalCalc_subst_formalExp
-- name    : GlobalTheory.FormalCalc.subst_formalExp
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T13:33:44.950083+00:00
-- url     : https://prove2.me/theorems/5a07d6fc-9062-4171-a476-8118ff0d275a
-- title:
--   Formal Calc: subst formal Exp
-- statement:
--   The Formal Calc construction uses the subst formal Exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FormalExpMulFormalExpNeg.lean#L123-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FormalExpMulFormalExpNeg.lean#L123-L127

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

theorem GlobalTheory.FormalCalc.subst_formalExp {a : σ → MvPowerSeries τ A} (ha : HasSubst a)
    {f : MvPowerSeries σ A} (hf : constantCoeff f = 0) :
    subst a (formalExp f) = formalExp (subst a f) := by sorry
