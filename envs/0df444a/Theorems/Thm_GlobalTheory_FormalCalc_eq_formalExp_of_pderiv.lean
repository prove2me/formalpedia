-- Prove2me | Theorems.Thm_GlobalTheory_FormalCalc_eq_formalExp_of_pderiv
-- name    : GlobalTheory.FormalCalc.eq_formalExp_of_pderiv
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:50:16.709703+00:00
-- url     : https://prove2.me/theorems/1f59f3c2-0801-47a7-ba92-27181ebd02a1
-- title:
--   Formal Calc: eq formal Exp of pderiv
-- statement:
--   The Formal Calc construction uses the eq formal Exp of pderiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FormalExpMulFormalExpNeg.lean#L59-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FormalExpMulFormalExpNeg.lean#L59-L72

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

theorem GlobalTheory.FormalCalc.eq_formalExp_of_pderiv {f u : MvPowerSeries σ A} (hf : constantCoeff f = 0)
    (hu : constantCoeff u = 1) (h : ∀ i, pderiv A i u = u * pderiv A i f) :
    u = formalExp f := by sorry
