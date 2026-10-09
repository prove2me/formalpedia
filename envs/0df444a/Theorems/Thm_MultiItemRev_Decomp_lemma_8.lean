-- Prove2me | Theorems.Thm_MultiItemRev_Decomp_lemma_8
-- name    : MultiItemRev.Decomp.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:24:25.369564+00:00
-- url     : https://prove2.me/theorems/be22e59a-d187-4801-b539-2b8880d7e5a8
-- title:
--   Lemma 8, p. 19 — Rev((Y,Z)1_{(Y,Z)∈A}) ≤ Rev(Y) + Val(Z1_{(Y,Z)∈A}) for independent Y, Z
-- statement:
--   **Lemma 8 (Marginal Mechanism on Subdomain).** Let $Y$ be a random valuation for $k_1 \ge 1$ goods and $Z$ one for $k_2 \ge 1$ goods, and let $A \subseteq \mathbb{R}^{k_1 + k_2}_+$ be a measurable set of values of $(Y, Z)$. If $Y$ and $Z$ are independent, then
--   $$
--   \mathrm{Rev}\big((Y,Z)\,\mathbf 1_{(Y,Z) \in A}\big) \le \mathrm{Rev}(Y) + \mathrm{Val}\big(Z\,\mathbf 1_{(Y,Z) \in A}\big),
--   $$
--   where $\mathrm{Val}(W) = \mathbb{E}[\sum_j W_j]$.
--
--   Any mechanism for both groups, restricted to the region $A$, earns at most the optimal revenue from the $Y$ goods alone plus the total expected value of the $Z$ goods on $A$. With Lemma 10 it bounds each of the two terms in the proof of Theorem 7.
--
--   **Formalization Note** Independence is encoded by taking the law of $(Y,Z)$ to be the product of the laws of $Y$ and $Z$ (`jointLaw`). $\mathrm{Val}(Z \mathbf 1_{(Y,Z)\in A})$ is $\mathrm{Val}$ of the image of the law of $(Y,Z)\mathbf 1_{(Y,Z)\in A}$ under $(y,z) \mapsto z$; it equals $\mathbb{E}[\sum_j Z_j \mathbf 1_{(Y,Z)\in A}]$. $A$ is assumed measurable.
-- source:
--   Hart and Nisan, Approximate Revenue Maximization with Multiple Items, arXiv:1204.1846v3, p. 19, Lemma 8

import Mathlib
import Definitions.Def_MultiItemRev_Decomp_Model

open MeasureTheory
open scoped NNReal ENNReal

namespace MultiItemRev.Decomp

theorem lemma_8 {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] [Nonempty ι₁] [Nonempty ι₂]
    (μY : Measure (ι₁ → ℝ≥0)) (μZ : Measure (ι₂ → ℝ≥0))
    [IsProbabilityMeasure μY] [IsProbabilityMeasure μZ]
    (A : Set (ι₁ ⊕ ι₂ → ℝ≥0)) (hA : MeasurableSet A) :
    Rev (lawOn (jointLaw μY μZ) A) ≤
      Rev μY + Val ((lawOn (jointLaw μY μZ) A).map zPart) := by sorry

end MultiItemRev.Decomp
