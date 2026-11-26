-- Prove2me | Theorems.Thm_LowRankUnivariateSOS_perpPair_snd
-- name    : LowRankUnivariateSOS.perpPair_snd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:53:23.291406+00:00
-- url     : https://prove2.me/theorems/4ca58c46-8bc7-5356-ae90-77f7e6e96dfa
-- title:
--   Low Rank Univariate SOS: perp Pair snd
-- statement:
--   The Low Rank Univariate SOS construction uses the perp Pair snd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/H1Case.lean#L37-L39
-- source:
--   https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/H1Case.lean#L37-L39

import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Ring
import Definitions.Def_LowRankUnivariateSOS_Certificate
import Definitions.Def_LowRankUnivariateSOS_H1Case
set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS

theorem LowRankUnivariateSOS.perpPair_snd (t : Poly) (u : UPair) :
    (perpPair t u).snd = t * u.fst := by sorry

attribute [defeq] LowRankUnivariateSOS.perpPair_snd
