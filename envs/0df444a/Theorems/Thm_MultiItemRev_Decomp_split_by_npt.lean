-- Prove2me | Theorems.Thm_MultiItemRev_Decomp_split_by_npt
-- name    : MultiItemRev.Decomp.split_by_npt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:24:39.789271+00:00
-- url     : https://prove2.me/theorems/f28cdb1e-edb2-4929-b13b-13f510c55f9a
-- title:
--   Proof of Theorem 7, p. 20 — Rev(Y,Z) ≤ Rev((Y,Z)1_{ΣY ≥ ΣZ}) + Rev((Y,Z)1_{ΣZ ≥ ΣY})
-- statement:
--   Let $X = (Y, Z)$ be a random valuation for two independent groups of goods, $Y$ for $k_1 \ge 1$ goods and $Z$ for $k_2 \ge 1$ goods. Then
--   $$
--   \mathrm{Rev}(Y, Z) \le \mathrm{Rev}\big((Y,Z)\,\mathbf 1_{\sum_i Y_i \ge \sum_j Z_j}\big) + \mathrm{Rev}\big((Y,Z)\,\mathbf 1_{\sum_j Z_j \ge \sum_i Y_i}\big).
--   $$
--
--   This is the first step of the proof of Theorem 7: by NPT (Proposition 6 (iii)) the revenue of a mechanism is at most the sum of its revenues on the two closed regions, which together cover the space (the diagonal $\sum_i Y_i = \sum_j Z_j$ is counted twice).
--
--   **Formalization Note** Independence is encoded by the product law of $Y$ and $Z$. Both regions are closed, as printed.
-- source:
--   Hart and Nisan, Approximate Revenue Maximization with Multiple Items, arXiv:1204.1846v3, p. 20, proof of Theorem 7, first display

import Mathlib
import Definitions.Def_MultiItemRev_Decomp_Model

open MeasureTheory
open scoped NNReal ENNReal

namespace MultiItemRev.Decomp

theorem split_by_npt {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] [Nonempty ι₁] [Nonempty ι₂]
    (μY : Measure (ι₁ → ℝ≥0)) (μZ : Measure (ι₂ → ℝ≥0))
    [IsProbabilityMeasure μY] [IsProbabilityMeasure μZ] :
    Rev (jointLaw μY μZ) ≤
      Rev (lawOn (jointLaw μY μZ) {x | sumZ x ≤ sumY x}) +
        Rev (lawOn (jointLaw μY μZ) {x | sumY x ≤ sumZ x}) := by sorry

end MultiItemRev.Decomp
