-- Prove2me | Theorems.Thm_GlobalTheory_MatrixBall_dotProduct_mulVec_eq_inner
-- name    : GlobalTheory.MatrixBall.dotProduct_mulVec_eq_inner
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:49:02.674276+00:00
-- url     : https://prove2.me/theorems/611a2a8f-5b3b-48df-a628-4c3d92139694
-- title:
--   Matrix Ball: dot Product mul Vec eq inner
-- statement:
--   The Matrix Ball construction uses the dot Product mul Vec eq inner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ConjTransposeBoostMulSignatureMulBoost.lean#L20-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ConjTransposeBoostMulSignatureMulBoost.lean#L20-L23

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

theorem GlobalTheory.MatrixBall.dotProduct_mulVec_eq_inner (M : Matrix n n ℂ) (v : n → ℂ) :
    star v ⬝ᵥ M *ᵥ v = ⟪(toLp 2 v : EuclideanSpace ℂ n), toEuclideanLin M (toLp 2 v)⟫_ℂ := by sorry
