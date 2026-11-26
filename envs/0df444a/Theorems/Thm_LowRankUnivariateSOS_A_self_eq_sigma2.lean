-- Prove2me | Theorems.Thm_LowRankUnivariateSOS_A_self_eq_sigma2
-- name    : LowRankUnivariateSOS.A_self_eq_sigma2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:52:58.553926+00:00
-- url     : https://prove2.me/theorems/d5daed42-1b9a-50e5-aa0b-57835671546d
-- title:
--   Low Rank Univariate SOS: A self eq sigma2
-- statement:
--   Substituting `v = u` into `A_u(v)` gives `σ(u)`. This is the elementary
--    identity that lets the FOCP condition immediately say something about the
--    objective itself.
--
--   Source: https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/Socp.lean#L96-L97
-- source:
--   https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/Socp.lean#L96-L97

import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Definitions.Def_LowRankUnivariateSOS_PolynomialModel
import Definitions.Def_LowRankUnivariateSOS_Socp
set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS

theorem LowRankUnivariateSOS.A_self_eq_sigma2 (u : UPair) : A u u = sigma2 u := by sorry
