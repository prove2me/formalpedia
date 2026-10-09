-- Prove2me | Theorems.Thm_MultiItemRev_Decomp_lemma_10
-- name    : MultiItemRev.Decomp.lemma_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:24:37.918922+00:00
-- url     : https://prove2.me/theorems/a7d408ed-cee0-4145-9fca-911904f1fb59
-- title:
--   Lemma 10, p. 20 — Val(Z1_{ΣY ≥ ΣZ}) ≤ BRev(Y) for independent Y, Z
-- statement:
--   **Lemma 10 (Smaller Value for Multiple Goods).** Let $Y$ be a random valuation for $k_1 \ge 1$ goods and $Z$ one for $k_2 \ge 1$ goods. If $Y$ and $Z$ are independent, then
--   $$
--   \mathrm{Val}\big(Z\,\mathbf 1_{\sum_i Y_i \ge \sum_j Z_j}\big) \le \mathrm{BRev}(Y).
--   $$
--
--   Together with Lemma 8 for the region $A = \{(y,z) : \sum_i y_i \ge \sum_j z_j\}$, this bounds the first term in the proof of Theorem 7 by $\mathrm{Rev}(Y) + \mathrm{BRev}(Y)$.
--
--   **Formalization Note** Independence is the product law of $Y$ and $Z$ (`jointLaw`); $\mathrm{Val}(Z \mathbf 1_{\sum_i Y_i \ge \sum_j Z_j})$ is $\mathrm{Val}$ of the image under $(y,z)\mapsto z$ of the law of $(Y,Z)$ multiplied by the indicator of the closed region $\{\sum_j z_j \le \sum_i y_i\}$.
-- source:
--   Hart and Nisan, Approximate Revenue Maximization with Multiple Items, arXiv:1204.1846v3, p. 20, Lemma 10

import Mathlib
import Definitions.Def_MultiItemRev_Decomp_Model

open MeasureTheory
open scoped NNReal ENNReal

namespace MultiItemRev.Decomp

theorem lemma_10 {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] [Nonempty ι₁] [Nonempty ι₂]
    (μY : Measure (ι₁ → ℝ≥0)) (μZ : Measure (ι₂ → ℝ≥0))
    [IsProbabilityMeasure μY] [IsProbabilityMeasure μZ] :
    Val ((lawOn (jointLaw μY μZ) {x | sumZ x ≤ sumY x}).map zPart) ≤ BRev μY := by sorry

end MultiItemRev.Decomp
