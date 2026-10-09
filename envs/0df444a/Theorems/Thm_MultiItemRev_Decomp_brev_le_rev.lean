-- Prove2me | Theorems.Thm_MultiItemRev_Decomp_brev_le_rev
-- name    : MultiItemRev.Decomp.brev_le_rev
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:24:57.485882+00:00
-- url     : https://prove2.me/theorems/a931045b-e32b-4840-8590-f9fa04c9c10e
-- title:
--   p. 18 — BRev ≤ Rev
-- statement:
--   Let $X$ be a $k$-good random valuation in $\mathbb{R}^k_+$, $k \ge 1$. Then
--   $$
--   \mathrm{BRev}(X) = \mathrm{Rev}(X_1 + \dots + X_k) \le \mathrm{Rev}(X).
--   $$
--
--   Selling all goods as one bundle is one particular way of selling them, so its optimal revenue cannot exceed the optimal revenue. This is the step from (6) to (7) in Theorem 7.
--
--   **Formalization Note** $\mathrm{BRev}(X)$ is the one-good optimal revenue of the law of $\sum_i X_i$; $\mathrm{Rev}(X)$ is the optimal revenue over the class $\mathcal M$ of the $k$-good model.
-- source:
--   Hart and Nisan, Approximate Revenue Maximization with Multiple Items, arXiv:1204.1846v3, p. 18, sentence after Theorem 7 ("because BRev≤Rev")

import Mathlib
import Definitions.Def_MultiItemRev_Decomp_Model

open MeasureTheory
open scoped NNReal ENNReal

namespace MultiItemRev.Decomp

theorem brev_le_rev {ι : Type*} [Fintype ι] [Nonempty ι]
    (μ : Measure (ι → ℝ≥0)) [IsProbabilityMeasure μ] :
    BRev μ ≤ Rev μ := by sorry

end MultiItemRev.Decomp
