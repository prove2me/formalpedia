-- Prove2me | Theorems.Thm_KernelRank_sum_expPoly_eq_truncForm
-- name    : KernelRank.sum_expPoly_eq_truncForm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T02:09:50.296113+00:00
-- url     : https://prove2.me/theorems/22086894-9748-4149-a259-3ae84a7711d8
-- title:
--   Kernel Rank: sum exp Poly eq trunc Form
-- statement:
--   Multinomial expansion of `expPoly P μ (∑ j, s j)` into `truncForm` terms.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/MultiComplexRank.lean#L824-L900
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/MultiComplexRank.lean#L824-L900

import Definitions.Def_KernelRankLean_ComplexRank
import Definitions.Def_KernelRankLean_MultiComplexRank
set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank

theorem KernelRank.sum_expPoly_eq_truncForm {ι : Type*} [Fintype ι] (d : ℕ) (rate : ι → ℂ)
    (P : ι → ℂ[X]) (s : Fin d → ℝ≥0) :
    (∑ i, expPoly (P i) (rate i) (∑ j, (s j : ℝ))) =
      truncForm d (fun i => (P i).natDegree + 1) (fun i => (P i).natDegree + 1)
        (fun i k => (k.factorial : ℂ) * (P i).coeff k)
        (fun j i q => ((s j : ℂ) ^ (q : ℕ) / ((q : ℕ).factorial : ℂ)) *
          exp (rate i * (s j : ℂ))) := by sorry
