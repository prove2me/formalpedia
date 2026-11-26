-- Prove2me | Theorems.Thm_LowRankUnivariateSOS_dot_zero_right
-- name    : LowRankUnivariateSOS.dot_zero_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:53:04.932383+00:00
-- url     : https://prove2.me/theorems/f15af25d-8f97-56e3-9318-03bfc6324fcd
-- title:
--   Low Rank Univariate SOS: dot zero right
-- statement:
--   The Low Rank Univariate SOS construction uses the dot zero right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/Socp.lean#L52-L53
-- source:
--   https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/Socp.lean#L52-L53

import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Definitions.Def_LowRankUnivariateSOS_PolynomialModel
import Definitions.Def_LowRankUnivariateSOS_Socp
set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS
variable {B : DotForm}

theorem LowRankUnivariateSOS.dot_zero_right (p : Poly) : B p 0 = 0 := by sorry
