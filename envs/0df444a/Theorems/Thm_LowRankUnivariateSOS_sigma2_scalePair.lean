-- Prove2me | Theorems.Thm_LowRankUnivariateSOS_sigma2_scalePair
-- name    : LowRankUnivariateSOS.sigma2_scalePair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:53:54.987241+00:00
-- url     : https://prove2.me/theorems/59fab68a-77f7-5362-a52a-5d4946ebf022
-- title:
--   Low Rank Univariate SOS: sigma2 scale Pair
-- statement:
--   The Low Rank Univariate SOS construction uses the sigma2 scale Pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/H1Case.lean#L72-L75
-- source:
--   https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/H1Case.lean#L72-L75

import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Ring
import Definitions.Def_LowRankUnivariateSOS_Certificate
import Definitions.Def_LowRankUnivariateSOS_H1Case
set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS

theorem LowRankUnivariateSOS.sigma2_scalePair (g : Poly) (u : UPair) :
    sigma2 (scalePair g u) = g ^ 2 * sigma2 u := by sorry
