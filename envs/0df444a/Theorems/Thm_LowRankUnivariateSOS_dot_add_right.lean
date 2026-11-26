-- Prove2me | Theorems.Thm_LowRankUnivariateSOS_dot_add_right
-- name    : LowRankUnivariateSOS.dot_add_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:53:00.169834+00:00
-- url     : https://prove2.me/theorems/ed9f133d-0c79-567e-92cc-fd081623f209
-- title:
--   Low Rank Univariate SOS: dot add right
-- statement:
--   The Low Rank Univariate SOS construction uses the dot add right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/Socp.lean#L37-L39
-- source:
--   https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/Socp.lean#L37-L39

import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Definitions.Def_LowRankUnivariateSOS_PolynomialModel
import Definitions.Def_LowRankUnivariateSOS_Socp
set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS
variable {B : DotForm}

theorem LowRankUnivariateSOS.dot_add_right (p q r : Poly) :
    B p (q + r) = B p q + B p r := by sorry
