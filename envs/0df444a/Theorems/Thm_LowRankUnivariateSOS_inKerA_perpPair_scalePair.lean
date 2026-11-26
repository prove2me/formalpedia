-- Prove2me | Theorems.Thm_LowRankUnivariateSOS_inKerA_perpPair_scalePair
-- name    : LowRankUnivariateSOS.inKerA_perpPair_scalePair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:54:19.807788+00:00
-- url     : https://prove2.me/theorems/f994c958-698c-467b-a14c-35f3345d1b94
-- title:
--   Low Rank Univariate SOS: in Ker A perp Pair scale Pair
-- statement:
--   The perpendicular pair `(-t u₂, t u₁)` lies in `ker(A_{g u})`. This is the
--    explicit kernel generator behind the cone terms appearing in condition (C2).
--
--   Source: https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/H1Case.lean#L79-L82
-- source:
--   https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/H1Case.lean#L79-L82

import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Ring
import Definitions.Def_LowRankUnivariateSOS_Certificate
import Definitions.Def_LowRankUnivariateSOS_H1Case
set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS

theorem LowRankUnivariateSOS.inKerA_perpPair_scalePair (g t : Poly) (u : UPair) :
    InKerA (scalePair g u) (perpPair t u) := by sorry
