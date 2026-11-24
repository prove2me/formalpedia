-- Prove2me | Theorems.Thm_GlobalTheory_MatrixBall_posDef_one_sub_conjTranspose_mul
-- name    : GlobalTheory.MatrixBall.posDef_one_sub_conjTranspose_mul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:20:56.939272+00:00
-- url     : https://prove2.me/theorems/12f3aea3-798c-4300-9f77-eebaf59609fd
-- title:
--   Matrix Ball: pos Def one sub conj Transpose mul
-- statement:
--   The Matrix Ball construction uses the pos Def one sub conj Transpose mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ConjTransposeBoostMulSignatureMulBoost.lean#L40-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ConjTransposeBoostMulSignatureMulBoost.lean#L40-L50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ConjTransposeBoostMulSignatureMulBoost
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix WithLp
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator InnerProductSpace
noncomputable section
open GlobalTheory
open GlobalTheory.MatrixBall
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

theorem GlobalTheory.MatrixBall.posDef_one_sub_conjTranspose_mul {Z : Matrix m n ℂ} (hZ : ‖Z‖ < 1) :
    (1 - Zᴴ * Z).PosDef := by sorry
