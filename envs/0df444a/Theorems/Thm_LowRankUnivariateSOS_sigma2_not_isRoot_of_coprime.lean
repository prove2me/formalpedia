-- Prove2me | Theorems.Thm_LowRankUnivariateSOS_sigma2_not_isRoot_of_coprime
-- name    : LowRankUnivariateSOS.sigma2_not_isRoot_of_coprime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:58:50.769561+00:00
-- url     : https://prove2.me/theorems/80a6f934-c2c5-4f4f-b50b-e72eb7c52b9b
-- title:
--   Low Rank Univariate SOS: sigma2 not is Root of coprime
-- statement:
--   If `u₁` and `u₂` are coprime, then `σ(u)=u₁²+u₂²` has no real root.
--    This is exactly the argument in `\Cref{prop:no-real-roots}`: a real zero of a
--    sum of two squares forces both coordinates to vanish at that point, hence they
--    share the linear factor `X-C x`, contradicting coprimality.
--
--   Source: https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/UnivariateAlgebraCore.lean#L57-L75
-- source:
--   https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/UnivariateAlgebraCore.lean#L57-L75

import Definitions.Def_LowRankUnivariateSOS_H1Case
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.EuclideanDomain
import Definitions.Def_LowRankUnivariateSOS_UnivariateAlgebraCore
set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS

theorem LowRankUnivariateSOS.sigma2_not_isRoot_of_coprime
    (u : UPair) (hu : IsCoprime u.fst u.snd) (x : ℝ) :
    ¬ Polynomial.IsRoot (sigma2 u) x := by sorry
