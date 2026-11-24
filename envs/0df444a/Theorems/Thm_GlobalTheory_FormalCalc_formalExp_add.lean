-- Prove2me | Theorems.Thm_GlobalTheory_FormalCalc_formalExp_add
-- name    : GlobalTheory.FormalCalc.formalExp_add
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T13:33:48.963855+00:00
-- url     : https://prove2.me/theorems/3de01d28-70c7-4890-81eb-c41a97745ed7
-- title:
--   Formal Calc: formal Exp add
-- statement:
--   The Formal Calc construction uses the formal Exp add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FormalExpMulFormalExpNeg.lean#L88-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FormalExpMulFormalExpNeg.lean#L88-L94

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

theorem GlobalTheory.FormalCalc.formalExp_add {f g : MvPowerSeries σ A} (hf : constantCoeff f = 0)
    (hg : constantCoeff g = 0) : formalExp (f + g) = formalExp f * formalExp g := by sorry
