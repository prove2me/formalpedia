-- Prove2me | Theorems.Thm_KernelRank_re_coeff_prod_eq_sum_re
-- name    : KernelRank.re_coeff_prod_eq_sum_re
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T02:18:47.633849+00:00
-- url     : https://prove2.me/theorems/e6fef0d0-95de-4955-af64-46901a6cc10f
-- title:
--   Kernel Rank: re coeff prod eq sum re
-- statement:
--   **Universal root-of-unity real decomposition for polynomial products (`d ≥ 2`, `k ≥ 0`).**
--   For complex polynomials `U₀, …, U_{d-1}` of degree at most `k`, `Re ([X^k] ∏ j, U_j(X))` is an
--   alternating sum of `R = 2 * (d - 1) * k + d` real `d`-way products. At `k = 0`, `R = d`,
--   recovering `re_prod_eq_sum_re` (`d ≥ 2`).
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/MultiRealRank.lean#L264-L660
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/MultiRealRank.lean#L264-L660

import Definitions.Def_KernelRankLean_MultiComplexRank
import Definitions.Def_KernelRankLean_RealExpPoly
import Definitions.Def_KernelRankLean_MultiRealRank
set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank

theorem KernelRank.re_coeff_prod_eq_sum_re {d : ℕ} (hd : 2 ≤ d) (k : ℕ)
    (U : Fin d → ℂ[X]) (hdeg : ∀ j, (U j).natDegree ≤ k) :
    ((∏ j : Fin d, U j).coeff k).re =
      (2 : ℝ) ^ (d - 1) / (2 * (d - 1) * k + d : ℕ) *
        ∑ r : Fin (2 * (d - 1) * k + d), (-1 : ℝ) ^ (r : ℕ) *
          ∏ j : Fin d,
            ((U j).eval (exp (2 * Real.pi * I * (r : ℕ) / (2 * (d - 1) * k + d : ℕ))) *
              exp (-Real.pi * I * (r : ℕ) * (2 * k + 1 : ℕ) /
                (2 * (d - 1) * k + d : ℕ))).re := by sorry
