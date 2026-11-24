-- Prove2me | Theorems.Thm_GlobalTheory_MatrixBall_norm_toEuclideanLin_le
-- name    : GlobalTheory.MatrixBall.norm_toEuclideanLin_le
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:21:08.883572+00:00
-- url     : https://prove2.me/theorems/5a59fad0-3a6f-4d0e-b689-c499ac2b1b22
-- title:
--   Matrix Ball: norm to Euclidean Lin le
-- statement:
--   The Matrix Ball construction uses the norm to Euclidean Lin le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ConjTransposeBoostMulSignatureMulBoost.lean#L16-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ConjTransposeBoostMulSignatureMulBoost.lean#L16-L18

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
omit [DecidableEq m]

theorem GlobalTheory.MatrixBall.norm_toEuclideanLin_le (M : Matrix m n ℂ) (x : EuclideanSpace ℂ n) :
    ‖toEuclideanLin M x‖ ≤ ‖M‖ * ‖x‖ := by sorry
