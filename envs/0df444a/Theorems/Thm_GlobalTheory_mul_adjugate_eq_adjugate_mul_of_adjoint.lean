-- Prove2me | Theorems.Thm_GlobalTheory_mul_adjugate_eq_adjugate_mul_of_adjoint
-- name    : GlobalTheory.mul_adjugate_eq_adjugate_mul_of_adjoint
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:12:42.922181+00:00
-- url     : https://prove2.me/theorems/fe3a8b5e-09ba-443f-8219-34d72103abb2
-- title:
--   Global Theory: mul adjugate eq adjugate mul of adjoint
-- statement:
--   The Global Theory construction uses the mul adjugate eq adjugate mul of adjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsUnimodularPosDefAdjointAction.lean#L69-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsUnimodularPosDefAdjointAction.lean#L69-L74

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIntMatrixTransposeMulEqSmulOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUnimodularPosDefAdjointAction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Kronecker
open GlobalTheory
variable {n q : Type} [Fintype n] [DecidableEq n] [Fintype q] [DecidableEq q]

theorem GlobalTheory.mul_adjugate_eq_adjugate_mul_of_adjoint (B P Q : Matrix n n ℤ) (hd : B.det ≠ 0)
    (h : P * B = B * Q) : Q * B.adjugate = B.adjugate * P := by sorry
