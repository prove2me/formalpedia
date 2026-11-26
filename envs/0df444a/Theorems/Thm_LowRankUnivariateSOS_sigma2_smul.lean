-- Prove2me | Theorems.Thm_LowRankUnivariateSOS_sigma2_smul
-- name    : LowRankUnivariateSOS.sigma2_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:53:48.458102+00:00
-- url     : https://prove2.me/theorems/93c86509-e411-59cf-a152-709d355df4b2
-- title:
--   Low Rank Univariate SOS: sigma2 smul
-- statement:
--   The Low Rank Univariate SOS construction uses the sigma2 smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/H1Case.lean#L62-L65
-- source:
--   https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/H1Case.lean#L62-L65

import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Ring
import Definitions.Def_LowRankUnivariateSOS_Certificate
import Definitions.Def_LowRankUnivariateSOS_H1Case
set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS

theorem LowRankUnivariateSOS.sigma2_smul (a : ℝ) (u : UPair) :
    sigma2 (a • u) = (a ^ 2 : ℝ) • sigma2 u := by sorry
