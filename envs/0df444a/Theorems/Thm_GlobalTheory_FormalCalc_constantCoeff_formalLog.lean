-- Prove2me | Theorems.Thm_GlobalTheory_FormalCalc_constantCoeff_formalLog
-- name    : GlobalTheory.FormalCalc.constantCoeff_formalLog
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:47:29.991582+00:00
-- url     : https://prove2.me/theorems/f0d3e00a-ca27-42fa-98c2-b20fa5284cd1
-- title:
--   Formal Calc: constant Coeff formal Log
-- statement:
--   The Formal Calc construction uses the constant Coeff formal Log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FormalExpMulFormalExpNeg.lean#L28-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FormalExpMulFormalExpNeg.lean#L28-L30

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

theorem GlobalTheory.FormalCalc.constantCoeff_formalLog {g : MvPowerSeries σ A} (hg : constantCoeff g = 1) :
    constantCoeff (formalLog g) = 0 := by sorry
