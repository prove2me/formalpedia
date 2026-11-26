-- Prove2me | Theorems.Thm_LowRankUnivariateSOS_inImageA_mul_of_isCoprime
-- name    : LowRankUnivariateSOS.inImageA_mul_of_isCoprime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:54:15.573469+00:00
-- url     : https://prove2.me/theorems/c397c84f-c967-41fe-ad48-442081ff7db3
-- title:
--   Low Rank Univariate SOS: in Image A mul of is Coprime
-- statement:
--   The scaled version of Bézout surjectivity: every multiple `g q` lies in
--    `im(A_{g u})` when the reduced pair `u` is coprime.
--
--   Source: https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/H1Case.lean#L155-L160
-- source:
--   https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/H1Case.lean#L155-L160

import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Ring
import Definitions.Def_LowRankUnivariateSOS_Certificate
import Definitions.Def_LowRankUnivariateSOS_H1Case
set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS

theorem LowRankUnivariateSOS.inImageA_mul_of_isCoprime (g q : Poly) (u : UPair)
    (hu : IsCoprime u.fst u.snd) :
    InImageA (scalePair g u) (g * q) := by sorry
