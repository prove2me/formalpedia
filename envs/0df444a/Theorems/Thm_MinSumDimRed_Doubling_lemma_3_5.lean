-- Prove2me | Theorems.Thm_MinSumDimRed_Doubling_lemma_3_5
-- name    : MinSumDimRed.Doubling.lemma_3_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T19:34:45.095121+00:00
-- url     : https://prove2.me/theorems/5b9d279b-b1ec-461d-a1dc-9aae2bbfae1c
-- title:
--   Lemma 3.5 — one-median charge: $|S|\sum_{y\in S}\|y-c^*\| \le \sum_{y,y'\in S}\|y-y'\|$
-- statement:
--   **Lemma 3.5** (One-Median Charge, p. 12). Let $S \subseteq \mathbb R^d$ be finite and let $c^*$ be an optimal center for $S$ under the 1-median objective, i.e. $\sum_{y \in S} \|y - c^*\| \le \sum_{y \in S} \|y - c\|$ for every $c \in \mathbb R^d$. Then
--   $$|S| \sum_{y \in S} \|y - c^*\| \le \sum_{y, y' \in S} \|y - y'\|.$$
--
--   Differences from the source:
--   - encoding: S ⊆ ℝ^d → S : Finset (Pt d); reason: the sums and |S| in the statement require S finite, as for every set to which the paper applies the lemma (clusters of a finite X)
--   - encoding: c* an optimal center for S under the 1-median objective → IsOneMedianCenter S c: c minimises c' ↦ Σ_{y∈S} ‖y − c'‖ over all of ℝ^d; reason: the definition of an optimal 1-median center; for S = ∅ every point qualifies and both sides are 0
-- source:
--   Asaf Dallal, Robert Krauthgamer, Dimension Reduction and Coresets for Min-Sum k-Clustering, arXiv:2610.38920 (version of November 2, 2026, SHA-256 13a9281e…), p. 12 (PDF 12), Lemma 3.5

import Mathlib
import Definitions.Def_MinSumDimRed_Doubling_Costs

namespace MinSumDimRed.Doubling

/-- Lemma 3.5 (One-Median Charge), p. 12: for a finite `S ⊆ ℝ^d` and an optimal 1-median center
`c*` of `S` (a minimiser over all of `ℝ^d`), `|S| ∑_{y∈S} ‖y - c*‖ ≤ ∑_{y,y'∈S} ‖y - y'‖`. -/
theorem lemma_3_5 {d : ℕ} (S : Finset (Pt d)) (c : Pt d) (hc : IsOneMedianCenter S c) :
    (S.card : ℝ) * ∑ y ∈ S, ‖y - c‖ ≤ ∑ y ∈ S, ∑ y' ∈ S, ‖y - y'‖ := by sorry

end MinSumDimRed.Doubling
