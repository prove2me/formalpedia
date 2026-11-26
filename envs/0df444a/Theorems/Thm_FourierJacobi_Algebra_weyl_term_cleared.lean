-- Prove2me | Theorems.Thm_FourierJacobi_Algebra_weyl_term_cleared
-- name    : FourierJacobi.Algebra.weyl_term_cleared
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:14:30.672845+00:00
-- url     : https://prove2.me/theorems/98190401-5756-5afc-985c-c308f5985074
-- title:
--   Algebra: weyl term cleared
-- statement:
--   The Algebra construction uses the weyl term cleared property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/WeylEvaluation.lean#L61-L69
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/WeylEvaluation.lean#L61-L69

import Definitions.Def_FourierJacobi_Algebra_WeylSum
import Definitions.Def_FourierJacobi_Algebra_WeylEvaluation
set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Algebra
variable {K : Type*} [Field K]
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

theorem FourierJacobi.Algebra.weyl_term_cleared (t a b d : K) (ha : a ≠ 0) (hb : b ≠ 0) (hd : d ≠ 0)
    (ha₁ : a - 1 ≠ 0) (hb₁ : b - 1 ≠ 0) (hab : a - b ≠ 0) (hab₁ : a * b - 1 ≠ 0)
    (i : Fin 8) (hD : weylKernelDenominator t a b d i ≠ 0) :
    weylCommonDenominator t a b d * weylTerms t a b d i =
      weylClearedTerms t a b d i := by sorry
