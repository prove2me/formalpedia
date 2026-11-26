-- Prove2me | Theorems.Thm_LowRankUnivariateSOS_no_real_roots_sigma_reduced
-- name    : LowRankUnivariateSOS.no_real_roots_sigma_reduced
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:58:41.163719+00:00
-- url     : https://prove2.me/theorems/b5bd963c-2658-45e8-8cb4-78837b553245
-- title:
--   Low Rank Univariate SOS: no real roots sigma reduced
-- statement:
--   The reduced pair produced by `gcd_sigma_decomposition` satisfies the
--    no-real-roots conclusion of `\Cref{prop:no-real-roots}`. This is an immediate
--    corollary of the previous coprime lemma.
--
--   Source: https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/UnivariateAlgebraCore.lean#L80-L84
-- source:
--   https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/UnivariateAlgebraCore.lean#L80-L84

import Definitions.Def_LowRankUnivariateSOS_H1Case
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.EuclideanDomain
import Definitions.Def_LowRankUnivariateSOS_UnivariateAlgebraCore
set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS

theorem LowRankUnivariateSOS.no_real_roots_sigma_reduced
    (u : UPair) (data : ReducedFactorization u) :
    SigmaReducedNoRealRoots data.u0 := by sorry
