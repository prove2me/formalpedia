-- Prove2me | Theorems.Thm_GlobalTheory_FormalCalc_mul_pderiv_formalLog
-- name    : GlobalTheory.FormalCalc.mul_pderiv_formalLog
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:47:31.601622+00:00
-- url     : https://prove2.me/theorems/95b4f2bd-1d4b-4594-a2b3-c49752834168
-- title:
--   Formal Calc: mul pderiv formal Log
-- statement:
--   The Formal Calc construction uses the mul pderiv formal Log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FormalExpMulFormalExpNeg.lean#L50-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FormalExpMulFormalExpNeg.lean#L50-L57

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

theorem GlobalTheory.FormalCalc.mul_pderiv_formalLog {g : MvPowerSeries σ A} (hg : constantCoeff g = 1) (i : σ) :
    g * pderiv A i (formalLog g) = pderiv A i g := by sorry
