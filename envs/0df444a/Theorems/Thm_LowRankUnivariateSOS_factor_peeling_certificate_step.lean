-- Prove2me | Theorems.Thm_LowRankUnivariateSOS_factor_peeling_certificate_step
-- name    : LowRankUnivariateSOS.factor_peeling_certificate_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:00:39.119535+00:00
-- url     : https://prove2.me/theorems/4f624e00-3ff2-5e05-85cf-dc77ac360257
-- title:
--   Low Rank Univariate SOS: factor peeling certificate step
-- statement:
--   This theorem isolates the output of the factor-peeling stage needed by the
--    final proof: from a nonzero reduced factorization `u = a·u₀`, one obtains a
--    new factor `g` coprime to `σ(u₀)` such that the residual is orthogonal to
--    `im(A_{g u₀})`. This is the formal version of the transformed condition (C3)
--    after peeling all bad factors.
--
--   Source: https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/RankTwoMain.lean#L27-L38
-- source:
--   https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/RankTwoMain.lean#L27-L38

import Definitions.Def_LowRankUnivariateSOS_UnivariateAlgebra
import Definitions.Def_LowRankUnivariateSOS_UnivariateSOS
import Definitions.Def_LowRankUnivariateSOS_RankTwoMain
set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS
variable {B : DotForm}

theorem LowRankUnivariateSOS.factor_peeling_certificate_step
    (p : Poly) (u : UPair) :
    IsSOS p → IsSOCP B p u →
      (data : ReducedFactorization u) → data.a ≠ 0 →
      ∃ a g : Poly, ∃ u0 : UPair,
        u = scalePair a u0 ∧ g ≠ 0 ∧ IsCoprime u0.fst u0.snd ∧
          IsCoprime g (sigma2 u0) ∧
            ImageOrthogonalResidual B p (scalePair a u0) (scalePair g u0) := by sorry
