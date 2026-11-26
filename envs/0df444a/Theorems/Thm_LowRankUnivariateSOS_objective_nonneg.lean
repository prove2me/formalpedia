-- Prove2me | Theorems.Thm_LowRankUnivariateSOS_objective_nonneg
-- name    : LowRankUnivariateSOS.objective_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:54:07.938915+00:00
-- url     : https://prove2.me/theorems/022cabda-6baa-57cf-a747-30c10545e37b
-- title:
--   Low Rank Univariate SOS: objective nonneg
-- statement:
--   The objective is always nonnegative because it is the quadratic form
--    associated to a positive-definite bilinear form, evaluated at the residual.
--
--   Source: https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/Socp.lean#L112-L114
-- source:
--   https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/Socp.lean#L112-L114

import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Definitions.Def_LowRankUnivariateSOS_PolynomialModel
import Definitions.Def_LowRankUnivariateSOS_Socp
set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS
variable {B : DotForm} [Fact B.toQuadraticMap.PosDef]

theorem LowRankUnivariateSOS.objective_nonneg (p : Poly) (u : UPair) : 0 ≤ objective B p u := by sorry
