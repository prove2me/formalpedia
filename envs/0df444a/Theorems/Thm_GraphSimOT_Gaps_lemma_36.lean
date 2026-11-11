-- Prove2me | Theorems.Thm_GraphSimOT_Gaps_lemma_36
-- name    : GraphSimOT.Gaps.lemma_36
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:07:52.744589+00:00
-- url     : https://prove2.me/theorems/ddcb9730-db31-4496-b116-bee93d8ea675
-- title:
--   Lemma 36 — an α-thin permutation transfers line-metric transport costs: Σ|x_i − y_π(i)| ≤ α Σ Q_ij |x_i − y_j|
-- statement:
--   Let $n\ge2$ (App. E.2), $Q\in\mathrm{DS}(n)$, and let $\pi$ be a permutation of $[n]$ whose permutation matrix $P_\pi$ is $\alpha$-thin with respect to $Q$ (Eq. (23)). Then for all $x, y\in\mathbb R^n$,
--   $$\sum_{i\in[n]}|x_i - y_{\pi(i)}|\ \le\ \alpha\sum_{i,j\in[n]}Q_{ij}\,|x_i - y_j|.$$
--
--   Thinness controls cuts; this lemma upgrades it to a transport inequality for the line metric, which Theorem 38 combines with the local agreement Lemma 37.
--
--   Differences from the source:
--   - encoding: indices in [n] = {1, …, n} → Fin n = {0, …, n − 1}; reason: relabelling of the index set; no instance changes
-- source:
--   Breitung, Gervens, Grohe, Graph Similarity Meets Optimal Transport, arXiv:2611.05048 (held version, sha256 1cd10e91…), p. 33, Lemma 36

import Mathlib
import Definitions.Def_GraphSimOT_Gaps_CutRounding

namespace GraphSimOT.Gaps

/-- Lemma 36 (App. E.2, p. 33): if the permutation matrix of `π` is `α`-thin with respect to
`Q ∈ DS(n)`, then for all `x, y ∈ ℝ^n`, `∑_i |x_i − y_{π(i)}| ≤ α ∑_{i,j} Q_ij |x_i − y_j|`. -/
theorem lemma_36 {n : ℕ} (hn : 2 ≤ n) (α : ℝ) (π : Equiv.Perm (Fin n))
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q ∈ doublyStochastic ℝ (Fin n))
    (hthin : IsThin α (π.permMatrix ℝ) Q) (x y : Fin n → ℝ) :
    ∑ i, |x i - y (π i)| ≤ α * ∑ i, ∑ j, Q i j * |x i - y j| := by sorry

end GraphSimOT.Gaps
