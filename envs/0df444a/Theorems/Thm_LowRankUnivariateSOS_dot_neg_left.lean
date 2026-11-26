-- Prove2me | Theorems.Thm_LowRankUnivariateSOS_dot_neg_left
-- name    : LowRankUnivariateSOS.dot_neg_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:53:04.284134+00:00
-- url     : https://prove2.me/theorems/d4f5d5c5-43e4-4d82-94cd-b3a1deea37d7
-- title:
--   Low Rank Univariate SOS: dot neg left
-- statement:
--   The Low Rank Univariate SOS construction uses the dot neg left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/Socp.lean#L55-L57
-- source:
--   https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/Socp.lean#L55-L57

import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Definitions.Def_LowRankUnivariateSOS_PolynomialModel
import Definitions.Def_LowRankUnivariateSOS_Socp
set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS
variable {B : DotForm}

theorem LowRankUnivariateSOS.dot_neg_left (p q : Poly) :
    B (-p) q = -B p q := by sorry
