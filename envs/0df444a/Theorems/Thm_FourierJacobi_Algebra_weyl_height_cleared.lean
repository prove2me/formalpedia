-- Prove2me | Theorems.Thm_FourierJacobi_Algebra_weyl_height_cleared
-- name    : FourierJacobi.Algebra.weyl_height_cleared
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:14:18.200685+00:00
-- url     : https://prove2.me/theorems/f634450d-27e0-5468-a46a-9cac65fc4afa
-- title:
--   Algebra: weyl height cleared
-- statement:
--   The Algebra construction uses the weyl height cleared property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/WeylEvaluation.lean#L35-L43
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/WeylEvaluation.lean#L35-L43

import Definitions.Def_FourierJacobi_Algebra_WeylSum
import Definitions.Def_FourierJacobi_Algebra_WeylEvaluation
set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Algebra
variable {K : Type*} [Field K]
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

theorem FourierJacobi.Algebra.weyl_height_cleared (t a b d : K) (ha : a ≠ 0) (hb : b ≠ 0) (i : Fin 8) :
    (a ^ 2 * b ^ 2 * weylScale a b i) *
      kernelNumerator t d (weylU a b i) (weylV a b i) =
      weylHeightNumerators t a b d i := by sorry
