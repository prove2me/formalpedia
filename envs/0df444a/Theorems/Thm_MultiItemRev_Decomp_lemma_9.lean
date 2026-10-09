-- Prove2me | Theorems.Thm_MultiItemRev_Decomp_lemma_9
-- name    : MultiItemRev.Decomp.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:24:24.166988+00:00
-- url     : https://prove2.me/theorems/ba21ef8d-d889-475b-a712-abaae0ed476b
-- title:
--   Lemma 9, p. 20 — Val(Z1_{Y≥Z}) ≤ Rev(Y) for independent one-dimensional Y, Z
-- statement:
--   **Lemma 9 (Smaller Value).** Let $Y$ and $Z$ be one-dimensional nonnegative random variables. If $Y$ and $Z$ are independent, then
--   $$
--   \mathrm{Val}\big(Z\,\mathbf 1_{Y \ge Z}\big) = \mathbb{E}\big[Z\,\mathbf 1_{Y \ge Z}\big] \le \mathrm{Rev}(Y).
--   $$
--
--   The expected value of $Z$ on the event that it is the smaller of the two values is at most the revenue obtainable from $Y$ alone. Applied to $\sum_i Y_i$ and $\sum_j Z_j$ it gives Lemma 10.
--
--   **Formalization Note** $Y$ and $Z$ have laws $\nu_Y$ and $\nu_Z$ on $[0,\infty)$; independence is the product law $\nu_Y \otimes \nu_Z$, and the expectation is the lower Lebesgue integral of $(y,z) \mapsto z\,\mathbf 1_{z \le y}$ in $[0,\infty]$.
-- source:
--   Hart and Nisan, Approximate Revenue Maximization with Multiple Items, arXiv:1204.1846v3, p. 20, Lemma 9

import Mathlib
import Definitions.Def_MultiItemRev_Decomp_Model

open MeasureTheory
open scoped NNReal ENNReal

namespace MultiItemRev.Decomp

theorem lemma_9 (νY νZ : Measure ℝ≥0) [IsProbabilityMeasure νY] [IsProbabilityMeasure νZ] :
    ∫⁻ yz, (if yz.2 ≤ yz.1 then (yz.2 : ℝ≥0∞) else 0) ∂(νY.prod νZ) ≤ Rev1 νY := by sorry

end MultiItemRev.Decomp
