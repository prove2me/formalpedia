-- Prove2me | Theorems.Thm_LowRankUnivariateSOS_dot_neg_right
-- name    : LowRankUnivariateSOS.dot_neg_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:53:00.660372+00:00
-- url     : https://prove2.me/theorems/1203fd82-0a12-4760-a8fe-db6bbfd34fb1
-- title:
--   Low Rank Univariate SOS: dot neg right
-- statement:
--   The Low Rank Univariate SOS construction uses the dot neg right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/Socp.lean#L59-L61
-- source:
--   https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/Socp.lean#L59-L61

import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Definitions.Def_LowRankUnivariateSOS_PolynomialModel
import Definitions.Def_LowRankUnivariateSOS_Socp
set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS
variable {B : DotForm}

theorem LowRankUnivariateSOS.dot_neg_right (p q : Poly) :
    B p (-q) = -B p q := by sorry
