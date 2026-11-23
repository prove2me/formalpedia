-- Prove2me | Theorems.Thm_GlobalTheory_FormalCalc_constantCoeff_formalExp
-- name    : GlobalTheory.FormalCalc.constantCoeff_formalExp
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:47:28.349481+00:00
-- url     : https://prove2.me/theorems/3bda2ce0-8489-4114-85f3-2d5a4cea6ed6
-- title:
--   Formal Calc: constant Coeff formal Exp
-- statement:
--   The Formal Calc construction uses the constant Coeff formal Exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FormalExpMulFormalExpNeg.lean#L21-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FormalExpMulFormalExpNeg.lean#L21-L26

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

theorem GlobalTheory.FormalCalc.constantCoeff_formalExp {f : MvPowerSeries σ A} (hf : constantCoeff f = 0) :
    constantCoeff (formalExp f) = 1 := by sorry
