-- Prove2me | Theorems.Thm_LowRankUnivariateSOS_dot_eq_zero_of_peeling_step
-- name    : LowRankUnivariateSOS.dot_eq_zero_of_peeling_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:59:29.597076+00:00
-- url     : https://prove2.me/theorems/ca08e7ea-a558-4929-9a61-3b780e3a87d3
-- title:
--   Low Rank Univariate SOS: dot eq zero of peeling step
-- statement:
--   One peeling witness is enough to prove orthogonality to a specific target
--    `q`. The proof follows the paper's Hessian-family argument: substitute the
--    family `v_η` into the SOCP inequality, note that the quadratic coefficient is
--    already zero by the previous stage, and conclude from nonnegativity for all
--    `η` that the linear coefficient `⟨q, σ(u)-p⟩` must vanish.
--
--   Source: https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/PeelingStep.lean#L121-L138
-- source:
--   https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/PeelingStep.lean#L121-L138

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_LowRankUnivariateSOS_FactoredCase
import Definitions.Def_LowRankUnivariateSOS_PeelingStep
set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS
variable {B : DotForm}

theorem LowRankUnivariateSOS.dot_eq_zero_of_peeling_step {p : Poly} {u uImgPrev : UPair} {q : Poly}
    (hsocp : IsSOCP B p u)
    (hprev : ImageOrthogonalResidual B p u uImgPrev)
    (hstep : PeelingStepWitness u uImgPrev q) :
    B q (residual p u) = 0 := by sorry
