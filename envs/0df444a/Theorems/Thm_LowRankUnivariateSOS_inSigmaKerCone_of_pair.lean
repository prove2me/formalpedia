-- Prove2me | Theorems.Thm_LowRankUnivariateSOS_inSigmaKerCone_of_pair
-- name    : LowRankUnivariateSOS.inSigmaKerCone_of_pair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:54:23.970387+00:00
-- url     : https://prove2.me/theorems/0fd5ae67-b9a2-4a23-9824-acda53fd907f
-- title:
--   Low Rank Univariate SOS: in Sigma Ker Cone of pair
-- statement:
--   The sum of two kernel-squares lies in `cone(σ(ker(A_u)))`. The proof is
--    exactly the cone bookkeeping from the paper: either keep the two generators
--    separate, or combine equal ones using a `sqrt 2` rescaling.
--
--   Source: https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/H1Case.lean#L95-L116
-- source:
--   https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/H1Case.lean#L95-L116

import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Ring
import Definitions.Def_LowRankUnivariateSOS_Certificate
import Definitions.Def_LowRankUnivariateSOS_H1Case
set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS

theorem LowRankUnivariateSOS.inSigmaKerCone_of_pair {u w₁ w₂ : UPair}
    (hw₁ : InKerA u w₁) (hw₂ : InKerA u w₂) :
    InSigmaKerCone u (sigma2 w₁ + sigma2 w₂) := by sorry
