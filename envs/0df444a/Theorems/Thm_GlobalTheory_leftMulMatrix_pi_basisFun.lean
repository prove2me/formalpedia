-- Prove2me | Theorems.Thm_GlobalTheory_leftMulMatrix_pi_basisFun
-- name    : GlobalTheory.leftMulMatrix_pi_basisFun
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:04:02.093262+00:00
-- url     : https://prove2.me/theorems/7defc21a-98f7-4ff7-923c-772e5860df87
-- title:
--   Global Theory: left Mul Matrix pi basis Fun
-- statement:
--   The Global Theory construction uses the left Mul Matrix pi basis Fun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/NormDetMulProdSqLeOfEntryLe.lean#L13-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/NormDetMulProdSqLeOfEntryLe.lean#L13-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LinearIndependentRealOfIntOfDiscrete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NormDetMulProdSqLeOfEntryLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Matrix
open Module Algebra
open GlobalTheory
variable {E : Type*} [CommRing E] {ι : Type*} [Fintype ι]

theorem GlobalTheory.leftMulMatrix_pi_basisFun [DecidableEq ι] (x : ι → E) :
    leftMulMatrix (Pi.basisFun E ι) x = Matrix.diagonal x := by sorry
