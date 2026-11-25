-- Prove2me | Theorems.Thm_GlobalTheory_FormalCalc_map_formalLog
-- name    : GlobalTheory.FormalCalc.map_formalLog
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:05:28.473854+00:00
-- url     : https://prove2.me/theorems/8f1199e3-c692-4f95-8912-427d38e59779
-- title:
--   Formal Calc: map formal Log
-- statement:
--   The Formal Calc construction uses the map formal Log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FormalExpMulFormalExpNeg.lean#L135-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FormalExpMulFormalExpNeg.lean#L135-L138

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

theorem GlobalTheory.FormalCalc.map_formalLog (φ : A →+* B) {g : MvPowerSeries σ A} (hg : constantCoeff g = 1) :
    map φ (formalLog g) = formalLog (map φ g) := by sorry
