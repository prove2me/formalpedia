-- Prove2me | Theorems.Thm_LowRankUnivariateSOS_hasPeelingWitness_of_factor_step
-- name    : LowRankUnivariateSOS.hasPeelingWitness_of_factor_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:59:33.670966+00:00
-- url     : https://prove2.me/theorems/e5e7564a-54a1-4baf-b2fd-b944b60f6eca
-- title:
--   Low Rank Univariate SOS: has Peeling Witness of factor step
-- statement:
--   A single `QuadraticFactorStep` gives the witness package required for one
--    peeling move. This is the local algebraic input used later by the recursive
--    schedule construction.
--
--   Source: https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/PeelingStep.lean#L244-L249
-- source:
--   https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/PeelingStep.lean#L244-L249

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_LowRankUnivariateSOS_FactoredCase
import Definitions.Def_LowRankUnivariateSOS_PeelingStep
set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS

theorem LowRankUnivariateSOS.hasPeelingWitness_of_factor_step {u u0 : UPair} {a gStart gNext : Poly}
    (hu : u = scalePair a u0)
    (hcop : IsCoprime u0.fst u0.snd)
    (hfg : QuadraticFactorStep u0 gStart gNext) :
    HasPeelingWitness u (scalePair gStart u0) (scalePair gNext u0) := by sorry
