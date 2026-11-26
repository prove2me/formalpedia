-- Prove2me | Theorems.Thm_LowRankUnivariateSOS_rankTwo_no_spurious_socp
-- name    : LowRankUnivariateSOS.rankTwo_no_spurious_socp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:00:52.247295+00:00
-- url     : https://prove2.me/theorems/d70cb450-fa12-508d-93cf-da127d07ad20
-- title:
--   Low Rank Univariate SOS: rank Two no spurious socp
-- statement:
--   Main theorem, corresponding to `\Cref{thm:main}` specialized to the rank-2
--    formal model. Every SOCP of the quadratic penalty objective has zero residual,
--    hence `σ(u) = p` and the point is globally optimal.
--
--    Proof sketch: reduce to `rankTwo_factored_h1_setup`, then invoke the abstract
--    factored `h = 1` argument from `FactoredCase`, which combines first-order
--    orthogonality, second-order nonnegativity, the hgroup decomposition, and the
--    factor-peeling transport.
--
--   Source: https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/RankTwoMain.lean#L116-L127
-- source:
--   https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/RankTwoMain.lean#L116-L127

import Definitions.Def_LowRankUnivariateSOS_UnivariateAlgebra
import Definitions.Def_LowRankUnivariateSOS_UnivariateSOS
import Definitions.Def_LowRankUnivariateSOS_RankTwoMain
set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS
variable {B : DotForm} [Fact B.toQuadraticMap.PosDef]

theorem LowRankUnivariateSOS.rankTwo_no_spurious_socp
    (p : Poly) (u : UPair)
    (hp : IsSOS p) (hsocp : IsSOCP B p u) :
    sigma2 u = p := by sorry
