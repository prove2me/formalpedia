-- Prove2me | Theorems.Thm_LowRankUnivariateSOS_factored_h1_residual_eq_zero
-- name    : LowRankUnivariateSOS.factored_h1_residual_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:54:47.731946+00:00
-- url     : https://prove2.me/theorems/48d96d20-f6d8-467e-8bfd-79ef5c4c6cea
-- title:
--   Low Rank Univariate SOS: factored h1 residual eq zero
-- statement:
--   This is the factor-rescaled form of the paper's `h = 1` decomposition.
--    Starting from `p = g q + s σ(u₀)`, it rewrites `p` as
--    `img(A_{g u₀}) + cone(σ(ker(A_{a u₀})))`, which is the form needed by the
--    abstract image-plus-cone lemma above.
--
--   Source: https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/FactoredCase.lean#L127-L138
-- source:
--   https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/FactoredCase.lean#L127-L138

import Mathlib.Tactic.Linarith
import Definitions.Def_LowRankUnivariateSOS_Socp
import Definitions.Def_LowRankUnivariateSOS_H1Case
import Definitions.Def_LowRankUnivariateSOS_FactoredCase
set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS
variable {B : DotForm} [Fact B.toQuadraticMap.PosDef]

theorem LowRankUnivariateSOS.factored_h1_residual_eq_zero
    (a g p q s : Poly) (u0 : UPair)
    (hg : g ≠ 0)
    (hcop : IsCoprime u0.fst u0.snd)
    (hs : IsSOS s)
    (hp : p = g * q + s * sigma2 u0)
    (himg : ImageOrthogonalResidual B p (scalePair a u0) (scalePair g u0))
    (hsocp : IsSOCP B p (scalePair a u0)) :
    residual p (scalePair a u0) = 0 := by sorry
