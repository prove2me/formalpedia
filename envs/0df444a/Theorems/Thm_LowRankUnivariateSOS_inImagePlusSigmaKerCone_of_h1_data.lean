-- Prove2me | Theorems.Thm_LowRankUnivariateSOS_inImagePlusSigmaKerCone_of_h1_data
-- name    : LowRankUnivariateSOS.inImagePlusSigmaKerCone_of_h1_data
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:54:28.4805+00:00
-- url     : https://prove2.me/theorems/6861f182-9c32-47e2-b8be-09f30abde787
-- title:
--   Low Rank Univariate SOS: in Image Plus Sigma Ker Cone of h1 data
-- statement:
--   This packages the paper's `h = 1` sufficient condition. If
--    `p = g q + s σ(u)` with `u` coprime and `s` SOS, then `p` lies in
--    `im(A_{g u}) + cone(σ(ker(A_{g u})))`, which is precisely condition (C2).
--
--   Source: https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/H1Case.lean#L165-L174
-- source:
--   https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/H1Case.lean#L165-L174

import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Ring
import Definitions.Def_LowRankUnivariateSOS_Certificate
import Definitions.Def_LowRankUnivariateSOS_H1Case
set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS

theorem LowRankUnivariateSOS.inImagePlusSigmaKerCone_of_h1_data
    (g p q s : Poly) (u : UPair)
    (hu : IsCoprime u.fst u.snd)
    (hs : IsSOS s)
    (hp : p = g * q + s * sigma2 u) :
    InImagePlusSigmaKerCone (scalePair g u) p := by sorry
