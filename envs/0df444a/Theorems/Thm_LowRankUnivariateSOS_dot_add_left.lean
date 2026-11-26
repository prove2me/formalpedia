-- Prove2me | Theorems.Thm_LowRankUnivariateSOS_dot_add_left
-- name    : LowRankUnivariateSOS.dot_add_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:52:56.500207+00:00
-- url     : https://prove2.me/theorems/6f695a41-6fbc-5362-97b2-7943fca32173
-- title:
--   Low Rank Univariate SOS: dot add left
-- statement:
--   The next simp lemmas are the algebraic identities saying that a bilinear
--    form behaves linearly in each argument. They are used repeatedly when
--    expanding the gradient and Hessian expressions from Definition
--    `\ref{def:socp}`.
--
--   Source: https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/Socp.lean#L33-L35
-- source:
--   https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/Socp.lean#L33-L35

import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Definitions.Def_LowRankUnivariateSOS_PolynomialModel
import Definitions.Def_LowRankUnivariateSOS_Socp
set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS
variable {B : DotForm}

theorem LowRankUnivariateSOS.dot_add_left (p q r : Poly) :
    B (p + q) r = B p r + B q r := by sorry
