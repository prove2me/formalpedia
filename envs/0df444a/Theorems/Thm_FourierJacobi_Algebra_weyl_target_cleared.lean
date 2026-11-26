-- Prove2me | Theorems.Thm_FourierJacobi_Algebra_weyl_target_cleared
-- name    : FourierJacobi.Algebra.weyl_target_cleared
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:14:41.898667+00:00
-- url     : https://prove2.me/theorems/e0cae8b0-fb91-52b8-9b6e-a2019263ad64
-- title:
--   Algebra: weyl target cleared
-- statement:
--   The Algebra construction uses the weyl target cleared property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/WeylEvaluation.lean#L118-L126
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/WeylEvaluation.lean#L118-L126

import Definitions.Def_FourierJacobi_Algebra_WeylSum
import Definitions.Def_FourierJacobi_Algebra_WeylEvaluation
set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Algebra
variable {K : Type*} [Field K]
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

theorem FourierJacobi.Algebra.weyl_target_cleared (t a b d : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hd : d ≠ 0)
    (hD : d₁ t a b d * d₂ t a b d ≠ 0) :
    weylCommonDenominator t a b d * weylClosedExpression t a b d =
      weylTargetNumerator t a b d := by sorry
