-- Prove2me | Theorems.Thm_GlobalTheory_FormalCalc_formalLog_pow
-- name    : GlobalTheory.FormalCalc.formalLog_pow
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:05:29.511803+00:00
-- url     : https://prove2.me/theorems/4d39bd01-c4de-46d4-b97c-a7ed84501ed2
-- title:
--   Formal Calc: formal Log pow
-- statement:
--   The Formal Calc construction uses the formal Log pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FormalExpMulFormalExpNeg.lean#L119-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FormalExpMulFormalExpNeg.lean#L119-L121

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

theorem GlobalTheory.FormalCalc.formalLog_pow (n : ℕ) {g : MvPowerSeries σ A} (hg : constantCoeff g = 1) :
    formalLog (g ^ n) = n • formalLog g := by sorry
