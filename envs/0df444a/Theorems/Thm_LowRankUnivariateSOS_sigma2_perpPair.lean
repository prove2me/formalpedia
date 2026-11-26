-- Prove2me | Theorems.Thm_LowRankUnivariateSOS_sigma2_perpPair
-- name    : LowRankUnivariateSOS.sigma2_perpPair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:53:52.587797+00:00
-- url     : https://prove2.me/theorems/4850f3f6-8ace-4ea3-96a0-387d8bc1a29e
-- title:
--   Low Rank Univariate SOS: sigma2 perp Pair
-- statement:
--   The Low Rank Univariate SOS construction uses the sigma2 perp Pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/H1Case.lean#L67-L70
-- source:
--   https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/H1Case.lean#L67-L70

import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Ring
import Definitions.Def_LowRankUnivariateSOS_Certificate
import Definitions.Def_LowRankUnivariateSOS_H1Case
set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS

theorem LowRankUnivariateSOS.sigma2_perpPair (t : Poly) (u : UPair) :
    sigma2 (perpPair t u) = t ^ 2 * sigma2 u := by sorry
