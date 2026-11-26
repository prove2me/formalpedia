-- Prove2me | Theorems.Thm_LowRankUnivariateSOS_dot_zero_left
-- name    : LowRankUnivariateSOS.dot_zero_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:53:01.998934+00:00
-- url     : https://prove2.me/theorems/8ee99509-f44c-4fa3-8168-483e411ac0a9
-- title:
--   Low Rank Univariate SOS: dot zero left
-- statement:
--   The Low Rank Univariate SOS construction uses the dot zero left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/Socp.lean#L49-L50
-- source:
--   https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/Socp.lean#L49-L50

import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Definitions.Def_LowRankUnivariateSOS_PolynomialModel
import Definitions.Def_LowRankUnivariateSOS_Socp
set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS
variable {B : DotForm}

theorem LowRankUnivariateSOS.dot_zero_left (p : Poly) : B 0 p = 0 := by sorry
