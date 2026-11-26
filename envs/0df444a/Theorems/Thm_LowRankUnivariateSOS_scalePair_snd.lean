-- Prove2me | Theorems.Thm_LowRankUnivariateSOS_scalePair_snd
-- name    : LowRankUnivariateSOS.scalePair_snd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:53:22.623032+00:00
-- url     : https://prove2.me/theorems/1a8e45e7-2866-4ec4-85d2-9d73e0e0b2e3
-- title:
--   Low Rank Univariate SOS: scale Pair snd
-- statement:
--   The Low Rank Univariate SOS construction uses the scale Pair snd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/H1Case.lean#L29-L31
-- source:
--   https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/H1Case.lean#L29-L31

import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Ring
import Definitions.Def_LowRankUnivariateSOS_Certificate
import Definitions.Def_LowRankUnivariateSOS_H1Case
set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS

theorem LowRankUnivariateSOS.scalePair_snd (g : Poly) (u : UPair) :
    (scalePair g u).snd = g * u.snd := by sorry

attribute [defeq] LowRankUnivariateSOS.scalePair_snd
