-- Prove2me | Theorems.Thm_KernelRank_coeff_revHassePoly_mul_prod_truncExpPoly
-- name    : KernelRank.coeff_revHassePoly_mul_prod_truncExpPoly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T02:09:39.057095+00:00
-- url     : https://prove2.me/theorems/381b03fe-2b68-495b-bb9a-978a1c729ba6
-- title:
--   Kernel Rank: coeff rev Hasse Poly mul prod trunc Exp Poly
-- statement:
--   `coeff k` of `revHassePoly P k (u j₀) * ∏ j ≠ j₀, truncExpPoly k (u j)` equals
--   `P.eval (∑ j, u j)` for `k = P.natDegree`.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/MultiComplexRank.lean#L201-L227
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/MultiComplexRank.lean#L201-L227

import Definitions.Def_KernelRankLean_ComplexRank
import Definitions.Def_KernelRankLean_MultiComplexRank
set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank

theorem KernelRank.coeff_revHassePoly_mul_prod_truncExpPoly {d : ℕ} (P : ℂ[X]) (j₀ : Fin d) (u : Fin d → ℂ) :
    (revHassePoly P P.natDegree (u j₀) *
      ∏ j ∈ Finset.univ.erase j₀, truncExpPoly P.natDegree (u j)).coeff P.natDegree =
      P.eval (∑ j : Fin d, u j) := by sorry
