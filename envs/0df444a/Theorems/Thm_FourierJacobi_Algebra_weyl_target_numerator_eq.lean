-- Prove2me | Theorems.Thm_FourierJacobi_Algebra_weyl_target_numerator_eq
-- name    : FourierJacobi.Algebra.weyl_target_numerator_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:15:05.523585+00:00
-- url     : https://prove2.me/theorems/a3770c35-b13b-4ef6-8631-b804f7315f02
-- title:
--   Algebra: weyl target numerator eq
-- statement:
--   The Algebra construction uses the weyl target numerator eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/WeylEvaluation.lean#L110-L116
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/WeylEvaluation.lean#L110-L116

import Definitions.Def_FourierJacobi_Algebra_WeylSum
import Definitions.Def_FourierJacobi_Algebra_WeylEvaluation
set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Algebra
variable {K : Type*} [Field K]
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

theorem FourierJacobi.Algebra.weyl_target_numerator_eq (t a b d : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    weylTargetNumerator t a b d =
      (weylWall a b * a ^ 2 * b ^ 2 * d * (a ^ 2 * b ^ 2 * d ^ 4)) *
        (satakeNumerator a b * (1 - t ^ 2) * n₁ t a b * n₂ t a b) := by sorry
