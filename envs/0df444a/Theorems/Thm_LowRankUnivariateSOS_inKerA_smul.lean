-- Prove2me | Theorems.Thm_LowRankUnivariateSOS_inKerA_smul
-- name    : LowRankUnivariateSOS.inKerA_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:54:17.230861+00:00
-- url     : https://prove2.me/theorems/aee21623-c956-5223-99bf-5ec36bf79537
-- title:
--   Low Rank Univariate SOS: in Ker A smul
-- statement:
--   The kernel is closed under real scalar multiplication. This is used when
--    two identical kernel generators are combined into a single term by scaling with
--    `sqrt 2`.
--
--   Source: https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/H1Case.lean#L87-L90
-- source:
--   https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/H1Case.lean#L87-L90

import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Ring
import Definitions.Def_LowRankUnivariateSOS_Certificate
import Definitions.Def_LowRankUnivariateSOS_H1Case
set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS

theorem LowRankUnivariateSOS.inKerA_smul {u w : UPair} (a : ℝ) (hw : InKerA u w) :
    InKerA u (a • w) := by sorry
