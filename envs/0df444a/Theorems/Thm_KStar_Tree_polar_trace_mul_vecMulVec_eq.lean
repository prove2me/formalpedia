-- Prove2me | Theorems.Thm_KStar_Tree_polar_trace_mul_vecMulVec_eq
-- name    : KStar.Tree.polar_trace_mul_vecMulVec_eq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:52:10.131698+00:00
-- url     : https://prove2.me/theorems/582230b6-86dd-495c-9256-e15a2346ac2e
-- title:
--   Tree: polar trace mul vec Mul Vec eq
-- statement:
--   The Tree construction uses the polar trace mul vec Mul Vec eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/ClassNumberBounds/CyclotomicTotient/PolarTraceMulVecMulVecEq.lean#L22-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/ClassNumberBounds/CyclotomicTotient/PolarTraceMulVecMulVecEq.lean#L22-L26

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_CyclotomicTotient_TwistTrace
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_CyclotomicTotient_PolarTraceMulVecMulVecEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open KStar KStar.Tree
open Matrix

theorem KStar.Tree.polar_trace_mul_vecMulVec_eq {A : Type} [CommRing A] {r : ℕ}
    (M : Matrix (Fin r) (Fin r) A) (a b : Fin r → A) :
    (M * Matrix.vecMulVec a b).trace = M.mulVec a ⬝ᵥ b := by sorry
