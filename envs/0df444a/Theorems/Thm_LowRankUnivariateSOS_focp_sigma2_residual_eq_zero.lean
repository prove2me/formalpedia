-- Prove2me | Theorems.Thm_LowRankUnivariateSOS_focp_sigma2_residual_eq_zero
-- name    : LowRankUnivariateSOS.focp_sigma2_residual_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:54:15.103094+00:00
-- url     : https://prove2.me/theorems/59d85897-9a18-4497-9ce6-c8326c26a875
-- title:
--   Low Rank Univariate SOS: focp sigma2 residual eq zero
-- statement:
--   Any FOCP satisfies `⟨σ(u), σ(u)-p⟩ = 0`. This is equation
--    `\eqref{eq:gradA}` evaluated at the special direction `v = u`, and it is used
--    throughout the certificate-style arguments.
--
--   Source: https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/Socp.lean#L102-L104
-- source:
--   https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/Socp.lean#L102-L104

import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Definitions.Def_LowRankUnivariateSOS_PolynomialModel
import Definitions.Def_LowRankUnivariateSOS_Socp
set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS

theorem LowRankUnivariateSOS.focp_sigma2_residual_eq_zero {p : Poly} {u : UPair} (h : IsFOCP B p u) :
    B (sigma2 u) (residual p u) = 0 := by sorry
