-- Prove2me | Theorems.Thm_FourierJacobi_Algebra_weyl_common_euler_factorization
-- name    : FourierJacobi.Algebra.weyl_common_euler_factorization
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T10:13:49.153824+00:00
-- url     : https://prove2.me/theorems/ae7627ff-507b-5a85-8ee6-e388831c3bd2
-- title:
--   Algebra: weyl common euler factorization
-- statement:
--   The Algebra construction uses the weyl common euler factorization property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/WeylEvaluation.lean#L94-L104
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/WeylEvaluation.lean#L94-L104

import Definitions.Def_FourierJacobi_Algebra_WeylSum
import Definitions.Def_FourierJacobi_Algebra_WeylEvaluation
set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Algebra
variable {K : Type*} [Field K]
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

theorem FourierJacobi.Algebra.weyl_common_euler_factorization (t a b d : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hd : d ≠ 0) :
    weylCommonDenominator t a b d =
      (weylWall a b * a ^ 2 * b ^ 2 * d * (a ^ 2 * b ^ 2 * d ^ 4)) *
        (d₁ t a b d * d₂ t a b d) := by sorry
