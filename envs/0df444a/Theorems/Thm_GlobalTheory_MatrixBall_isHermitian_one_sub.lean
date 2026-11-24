-- Prove2me | Theorems.Thm_GlobalTheory_MatrixBall_isHermitian_one_sub
-- name    : GlobalTheory.MatrixBall.isHermitian_one_sub
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T18:21:11.50495+00:00
-- url     : https://prove2.me/theorems/bb82462e-6a19-4a76-ab14-ce4d75fcc282
-- title:
--   Matrix Ball: is Hermitian one sub
-- statement:
--   The Matrix Ball construction uses the is Hermitian one sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ConjTransposeBoostMulSignatureMulBoost.lean#L37-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ConjTransposeBoostMulSignatureMulBoost.lean#L37-L38

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
omit [DecidableEq n]

theorem GlobalTheory.MatrixBall.isHermitian_one_sub [DecidableEq n] (M : Matrix m n ℂ) : (1 - Mᴴ * M).IsHermitian := by sorry
