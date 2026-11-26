-- Prove2me | Theorems.Thm_LowRankUnivariateSOS_hgroup_affine
-- name    : LowRankUnivariateSOS.hgroup_affine
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:00:32.984242+00:00
-- url     : https://prove2.me/theorems/820d8065-cf70-5c09-87db-6fbd417b5f31
-- title:
--   Low Rank Univariate SOS: hgroup affine
-- statement:
--   Affine hgroup lemma, corresponding to the affine version of
--    `\Cref{lem:hgroup}` proved in the paper just before the projective statement.
--    If `p` and `q` are SOS and `g` is coprime to `q`, then `p` can be written as
--    `g·t + s·q` with `s` still SOS.
--
--    Proof sketch: choose Bézout coefficients `a,b` with `a g + b q = 1`; then
--    `b² p q` is SOS, and a direct algebraic identity shows that
--    `g * (p * (2a - a² g)) + (b² p q) * q = p`. This is the Lean compression of
--    the paper's congruence argument modulo `g`.
--
--   Source: https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/UnivariateSOS.lean#L28-L54
-- source:
--   https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/UnivariateSOS.lean#L28-L54

import Definitions.Def_LowRankUnivariateSOS_UnivariateAlgebraCore
import Mathlib.Tactic.Ring
import Definitions.Def_LowRankUnivariateSOS_UnivariateSOS
set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS

theorem LowRankUnivariateSOS.hgroup_affine
    (g p q : Poly) :
    IsSOS p → IsSOS q → IsCoprime g q →
      ∃ s t : Poly, IsSOS s ∧ p = g * t + s * q := by sorry
