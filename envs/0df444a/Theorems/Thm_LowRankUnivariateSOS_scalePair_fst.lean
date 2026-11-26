-- Prove2me | Theorems.Thm_LowRankUnivariateSOS_scalePair_fst
-- name    : LowRankUnivariateSOS.scalePair_fst
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:53:16.913026+00:00
-- url     : https://prove2.me/theorems/7df5476a-16b2-59a1-9426-9fd46d428ea6
-- title:
--   Low Rank Univariate SOS: scale Pair fst
-- statement:
--   Coordinate formulas for `scalePair`, `perpPair`, and scalar multiplication.
--    These are bookkeeping lemmas used to keep later polynomial identities readable.
--
--   Source: https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/H1Case.lean#L25-L27
-- source:
--   https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/H1Case.lean#L25-L27

import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Ring
import Definitions.Def_LowRankUnivariateSOS_Certificate
import Definitions.Def_LowRankUnivariateSOS_H1Case
set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS

theorem LowRankUnivariateSOS.scalePair_fst (g : Poly) (u : UPair) :
    (scalePair g u).fst = g * u.fst := by sorry

attribute [defeq] LowRankUnivariateSOS.scalePair_fst
