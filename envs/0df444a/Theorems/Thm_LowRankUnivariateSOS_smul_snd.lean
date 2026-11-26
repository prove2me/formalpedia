-- Prove2me | Theorems.Thm_LowRankUnivariateSOS_smul_snd
-- name    : LowRankUnivariateSOS.smul_snd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:53:18.016609+00:00
-- url     : https://prove2.me/theorems/77864e0d-43e4-5502-8e46-ad1f50a5a898
-- title:
--   Low Rank Univariate SOS: smul snd
-- statement:
--   The Low Rank Univariate SOS construction uses the smul snd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/H1Case.lean#L45-L47
-- source:
--   https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/H1Case.lean#L45-L47

import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Ring
import Definitions.Def_LowRankUnivariateSOS_Certificate
import Definitions.Def_LowRankUnivariateSOS_H1Case
set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS

theorem LowRankUnivariateSOS.smul_snd (a : ℝ) (u : UPair) :
    (a • u).snd = a • u.snd := by sorry

attribute [defeq] LowRankUnivariateSOS.smul_snd
