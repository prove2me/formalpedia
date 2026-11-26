-- Prove2me | Theorems.Thm_LowRankUnivariateSOS_dot_smul_right
-- name    : LowRankUnivariateSOS.dot_smul_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:53:01.868383+00:00
-- url     : https://prove2.me/theorems/3bcb8f2a-0690-51f1-a25d-ee92c08071d7
-- title:
--   Low Rank Univariate SOS: dot smul right
-- statement:
--   The Low Rank Univariate SOS construction uses the dot smul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/Socp.lean#L45-L47
-- source:
--   https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/Socp.lean#L45-L47

import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Definitions.Def_LowRankUnivariateSOS_PolynomialModel
import Definitions.Def_LowRankUnivariateSOS_Socp
set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS
variable {B : DotForm}

theorem LowRankUnivariateSOS.dot_smul_right (a : ℝ) (p q : Poly) :
    B p (a • q) = a * B p q := by sorry
