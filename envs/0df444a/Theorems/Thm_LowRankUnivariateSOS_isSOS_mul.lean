-- Prove2me | Theorems.Thm_LowRankUnivariateSOS_isSOS_mul
-- name    : LowRankUnivariateSOS.isSOS_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:00:31.039736+00:00
-- url     : https://prove2.me/theorems/55f1a15c-4618-561e-9afa-bc4fc3399284
-- title:
--   Low Rank Univariate SOS: is SOS mul
-- statement:
--   The product of two binary sums of two squares is again a binary sum of two
--    squares. This is the classical two-squares identity, and it is the algebraic
--    engine behind the SOS multiplier constructed in the hgroup lemma.
--
--   Source: https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/UnivariateSOS.lean#L11-L17
-- source:
--   https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/UnivariateSOS.lean#L11-L17

import Definitions.Def_LowRankUnivariateSOS_UnivariateAlgebraCore
import Mathlib.Tactic.Ring
import Definitions.Def_LowRankUnivariateSOS_UnivariateSOS
set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS

theorem LowRankUnivariateSOS.isSOS_mul {p q : Poly}
    (hp : IsSOS p) (hq : IsSOS q) :
    IsSOS (p * q) := by sorry
