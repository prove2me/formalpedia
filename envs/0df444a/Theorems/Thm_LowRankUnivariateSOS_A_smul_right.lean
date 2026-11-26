-- Prove2me | Theorems.Thm_LowRankUnivariateSOS_A_smul_right
-- name    : LowRankUnivariateSOS.A_smul_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:53:29.230116+00:00
-- url     : https://prove2.me/theorems/4755d50d-1181-4aa1-abac-fbcf7e968dfb
-- title:
--   Low Rank Univariate SOS: A smul right
-- statement:
--   The Low Rank Univariate SOS construction uses the A smul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/H1Case.lean#L57-L60
-- source:
--   https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/H1Case.lean#L57-L60

import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Ring
import Definitions.Def_LowRankUnivariateSOS_Certificate
import Definitions.Def_LowRankUnivariateSOS_H1Case
set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS

theorem LowRankUnivariateSOS.A_smul_right (a : ℝ) (u v : UPair) :
    A u (a • v) = a • A u v := by sorry
