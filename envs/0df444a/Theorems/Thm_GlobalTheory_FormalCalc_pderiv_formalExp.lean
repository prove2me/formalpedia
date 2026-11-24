-- Prove2me | Theorems.Thm_GlobalTheory_FormalCalc_pderiv_formalExp
-- name    : GlobalTheory.FormalCalc.pderiv_formalExp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:50:24.312961+00:00
-- url     : https://prove2.me/theorems/b95cb891-f274-4853-a242-fa439cb86ca6
-- title:
--   Formal Calc: pderiv formal Exp
-- statement:
--   The Formal Calc construction uses the pderiv formal Exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FormalExpMulFormalExpNeg.lean#L36-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FormalExpMulFormalExpNeg.lean#L36-L39

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

theorem GlobalTheory.FormalCalc.pderiv_formalExp {f : MvPowerSeries σ A} (hf : constantCoeff f = 0) (i : σ) :
    pderiv A i (formalExp f) = formalExp f * pderiv A i f := by sorry
