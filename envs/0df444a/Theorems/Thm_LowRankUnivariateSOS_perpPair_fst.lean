-- Prove2me | Theorems.Thm_LowRankUnivariateSOS_perpPair_fst
-- name    : LowRankUnivariateSOS.perpPair_fst
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:53:20.077283+00:00
-- url     : https://prove2.me/theorems/af51b4fc-9db3-5b57-8373-e196e553591e
-- title:
--   Low Rank Univariate SOS: perp Pair fst
-- statement:
--   The Low Rank Univariate SOS construction uses the perp Pair fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/H1Case.lean#L33-L35
-- source:
--   https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/H1Case.lean#L33-L35

import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Ring
import Definitions.Def_LowRankUnivariateSOS_Certificate
import Definitions.Def_LowRankUnivariateSOS_H1Case
set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS

theorem LowRankUnivariateSOS.perpPair_fst (t : Poly) (u : UPair) :
    (perpPair t u).fst = -t * u.snd := by sorry

attribute [defeq] LowRankUnivariateSOS.perpPair_fst
