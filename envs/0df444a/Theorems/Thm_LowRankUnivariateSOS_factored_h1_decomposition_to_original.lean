-- Prove2me | Theorems.Thm_LowRankUnivariateSOS_factored_h1_decomposition_to_original
-- name    : LowRankUnivariateSOS.factored_h1_decomposition_to_original
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:54:44.681285+00:00
-- url     : https://prove2.me/theorems/9ff49f8d-e7b4-46bf-969d-72efcf837d5f
-- title:
--   Low Rank Univariate SOS: factored h1 decomposition to original
-- statement:
--   Converts the explicit `h = 1` decomposition `p = g q + s σ(u₀)` into the
--    image-plus-cone form needed by the abstract SOCP argument, but now relative to
--    the original scale `a·u₀` instead of the reduced scale `g·u₀`.
--
--   Source: https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/FactoredCase.lean#L24-L39
-- source:
--   https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/FactoredCase.lean#L24-L39

import Mathlib.Tactic.Linarith
import Definitions.Def_LowRankUnivariateSOS_Socp
import Definitions.Def_LowRankUnivariateSOS_H1Case
import Definitions.Def_LowRankUnivariateSOS_FactoredCase
set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS

theorem LowRankUnivariateSOS.factored_h1_decomposition_to_original
    (a g p q s : Poly) (u0 : UPair)
    (hg : g ≠ 0)
    (hcop : IsCoprime u0.fst u0.snd)
    (hs : IsSOS s)
    (hp : p = g * q + s * sigma2 u0) :
    ∃ imgPart : Poly, ∃ ws : Finset UPair,
      InImageA (scalePair g u0) imgPart ∧
        (∀ w ∈ ws, InKerA (scalePair a u0) w) ∧
        p = imgPart + ws.sum sigma2 := by sorry
