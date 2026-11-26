-- Prove2me | Theorems.Thm_LowRankUnivariateSOS_dot_smul_left
-- name    : LowRankUnivariateSOS.dot_smul_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:52:59.001291+00:00
-- url     : https://prove2.me/theorems/f9a359cd-9921-5a66-8e14-66acc21469ae
-- title:
--   Low Rank Univariate SOS: dot smul left
-- statement:
--   The Low Rank Univariate SOS construction uses the dot smul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/Socp.lean#L41-L43
-- source:
--   https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/Socp.lean#L41-L43

import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Definitions.Def_LowRankUnivariateSOS_PolynomialModel
import Definitions.Def_LowRankUnivariateSOS_Socp
set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS
variable {B : DotForm}

theorem LowRankUnivariateSOS.dot_smul_left (a : ℝ) (p q : Poly) :
    B (a • p) q = a * B p q := by sorry
