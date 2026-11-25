-- Prove2me | Theorems.Thm_GlobalTheory_FormalCalc_subst_formalLog
-- name    : GlobalTheory.FormalCalc.subst_formalLog
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:05:10.546862+00:00
-- url     : https://prove2.me/theorems/6b565c6c-9b83-5bb2-b363-7d507714a7bb
-- title:
--   Formal Calc: subst formal Log
-- statement:
--   The Formal Calc construction uses the subst formal Log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FormalExpMulFormalExpNeg.lean#L129-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FormalExpMulFormalExpNeg.lean#L129-L133

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

theorem GlobalTheory.FormalCalc.subst_formalLog {a : σ → MvPowerSeries τ A} (ha : HasSubst a)
    {g : MvPowerSeries σ A} (hg : constantCoeff g = 1) :
    subst a (formalLog g) = formalLog (subst a g) := by sorry
