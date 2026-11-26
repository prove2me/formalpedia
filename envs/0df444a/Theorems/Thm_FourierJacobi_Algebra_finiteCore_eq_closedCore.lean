-- Prove2me | Theorems.Thm_FourierJacobi_Algebra_finiteCore_eq_closedCore
-- name    : FourierJacobi.Algebra.finiteCore_eq_closedCore
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:17:13.954151+00:00
-- url     : https://prove2.me/theorems/19d9ca43-5da4-4048-a7d0-5063af5c8f58
-- title:
--   Algebra: finite Core eq closed Core
-- statement:
--   The Algebra construction uses the finite Core eq closed Core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/FiniteCalculation.lean#L39-L58
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/FiniteCalculation.lean#L39-L58

import Definitions.Def_FourierJacobi_Algebra_WeylEvaluation
import Definitions.Def_FourierJacobi_Algebra_FiniteCalculation
set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Algebra
variable {K : Type*} [Field K]

theorem FourierJacobi.Algebra.finiteCore_eq_closedCore (t a b d : K) (h : FiniteRegular t a b d) :
    finiteCore t a b d = closedCore t a b d := by sorry
