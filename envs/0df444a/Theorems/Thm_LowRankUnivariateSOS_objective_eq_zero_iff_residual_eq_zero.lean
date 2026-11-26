-- Prove2me | Theorems.Thm_LowRankUnivariateSOS_objective_eq_zero_iff_residual_eq_zero
-- name    : LowRankUnivariateSOS.objective_eq_zero_iff_residual_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:54:12.740958+00:00
-- url     : https://prove2.me/theorems/2b58d410-c7b7-4339-ace9-f7155032a5d2
-- title:
--   Low Rank Univariate SOS: objective eq zero iff residual eq zero
-- statement:
--   For a positive-definite bilinear form, the objective vanishes exactly when
--    the residual vanishes. This is the formal bridge from the analytic statement
--    `f_p(u)=0` to the algebraic statement `σ(u)=p`.
--
--   Source: https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/Socp.lean#L119-L128
-- source:
--   https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/Socp.lean#L119-L128

import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Definitions.Def_LowRankUnivariateSOS_PolynomialModel
import Definitions.Def_LowRankUnivariateSOS_Socp
set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS
variable {B : DotForm} [Fact B.toQuadraticMap.PosDef]

theorem LowRankUnivariateSOS.objective_eq_zero_iff_residual_eq_zero {p : Poly} {u : UPair} :
    objective B p u = 0 ↔ residual p u = 0 := by sorry
