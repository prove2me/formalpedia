-- Prove2me | Theorems.Thm_LowRankUnivariateSOS_rankTwo_factored_h1_setup
-- name    : LowRankUnivariateSOS.rankTwo_factored_h1_setup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:01:08.013269+00:00
-- url     : https://prove2.me/theorems/8ffd6c8b-488f-474b-bbe0-52fb3c9a5fd1
-- title:
--   Low Rank Univariate SOS: rank Two factored h1 setup
-- statement:
--   This is the final reduction to the `h = 1` case. It packages the proof's
--    two main algebraic ingredients:
--    1. factor peeling, which produces a coprime transformed image;
--    2. the hgroup lemma, which writes `p` in the form `g q + s σ(u₀)`.
--    Together they yield the decomposition required by the abstract `h = 1`
--    residual-vanishing lemma.
--
--   Source: https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/RankTwoMain.lean#L74-L106
-- source:
--   https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/RankTwoMain.lean#L74-L106

import Definitions.Def_LowRankUnivariateSOS_UnivariateAlgebra
import Definitions.Def_LowRankUnivariateSOS_UnivariateSOS
import Definitions.Def_LowRankUnivariateSOS_RankTwoMain
set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS
variable {B : DotForm} [Fact B.toQuadraticMap.PosDef]

theorem LowRankUnivariateSOS.rankTwo_factored_h1_setup
    (p : Poly) (u : UPair) :
    IsSOS p → IsSOCP B p u →
      ∃ a g q s : Poly, ∃ u0 : UPair,
        u = scalePair a u0 ∧ g ≠ 0 ∧ IsCoprime u0.fst u0.snd ∧ IsSOS s ∧
          p = g * q + s * sigma2 u0 ∧
            ImageOrthogonalResidual B p (scalePair a u0) (scalePair g u0) := by sorry
