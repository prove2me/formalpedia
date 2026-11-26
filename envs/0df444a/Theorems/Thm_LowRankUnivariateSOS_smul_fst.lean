-- Prove2me | Theorems.Thm_LowRankUnivariateSOS_smul_fst
-- name    : LowRankUnivariateSOS.smul_fst
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:53:24.424872+00:00
-- url     : https://prove2.me/theorems/40f1e1a9-e14e-4ffc-9816-8e66973db7ed
-- title:
--   Low Rank Univariate SOS: smul fst
-- statement:
--   The Low Rank Univariate SOS construction uses the smul fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/H1Case.lean#L41-L43
-- source:
--   https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/H1Case.lean#L41-L43

import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Ring
import Definitions.Def_LowRankUnivariateSOS_Certificate
import Definitions.Def_LowRankUnivariateSOS_H1Case
set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS

theorem LowRankUnivariateSOS.smul_fst (a : ℝ) (u : UPair) :
    (a • u).fst = a • u.fst := by sorry

attribute [defeq] LowRankUnivariateSOS.smul_fst
