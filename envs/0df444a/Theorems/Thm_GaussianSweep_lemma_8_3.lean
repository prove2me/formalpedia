-- Prove2me | Theorems.Thm_GaussianSweep_lemma_8_3
-- name    : GaussianSweep.lemma_8_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:53:05.806189+00:00
-- url     : https://prove2.me/theorems/25545570-dbe7-4c43-adbc-c1c262b7ec44
-- title:
--   Lemma 8.3 — connector order: $j - c(j) \le \max(0, k-|P|) + 1$
-- statement:
--   Let $Q$ be a finite set with $k$ elements and let $P$ be a finite set of items, each item $p$ having a nonempty set $e(p) \subseteq Q$ of at most two endpoints. For an ordering $q_1, \dots, q_k$ of $Q$ and $0 \le j \le k$, let $c(j)$ be the number of items $p$ with $e(p) \subseteq \{q_1, \dots, q_j\}$. Then some ordering satisfies
--   $$
--   j - c(j) \le \max(0, k - |P|) + 1 \qquad \text{for all } 0 \le j \le k .
--   $$
--   This purely combinatorial ordering lemma controls the width of the connector bags that switch the layout from inner to outer frontiers at threshold zero.
--
--   **Formalization Note** An ordering is a bijection from $\{0, \dots, k-1\}$ to $Q$, so $\{q_1, \dots, q_j\}$ is the image of the first $j$ indices. The inequality is in the integers.
--
--   Differences from the source:
--   - encoding: an ordering q_1, …, q_k of Q → a bijection q : Fin k ≃ Q (0-based), with {q_1, …, q_j} = {q i | i < j}; reason: same orderings
--   - encoding: finite sets Q and P, k = |Q| → finite types Q and P (Fintype), k = card Q; reason: every finite set is such a type; same instances
--   - encoding: the inequality (8.3) between integers → the same inequality in ℤ; reason: j − c(j) and k − |P| may be negative
-- source:
--   Gaspers, Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Lemma 8.3, Eq. (8.3), p.46 (PDF p.48)

import Mathlib

namespace GaussianSweep

/-- Lemma 8.3 (connector order) (Gaspers, *Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms*, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Lemma 8.3, Eq. (8.3), p.46 (PDF p.48)). Let `Q` be a
finite set with `k` elements and `P` a finite set of items, each item `p` having a nonempty set
`e(p) ⊆ Q` of at most two endpoints. For an ordering `q₁, …, q_k` of `Q` and `0 ≤ j ≤ k`, let
`c(j)` be the number of items `p` with `e(p) ⊆ {q₁, …, q_j}`. Then some ordering satisfies
`j − c(j) ≤ max(0, k − |P|) + 1` for all `0 ≤ j ≤ k`.

**Formalization Note** `Q` and `P` are finite types; an ordering is a bijection
`q : Fin k ≃ Q` (0-based, so `{q₁, …, q_j}` is `{q i | i < j}` and `e(p) ⊆ {q₁, …, q_j}` is
`∀ x ∈ e p, q⁻¹ x < j`). The inequality is in `ℤ`. -/
theorem lemma_8_3 {Q P : Type} [Fintype Q] [DecidableEq Q] [Fintype P] (e : P → Finset Q)
    (he : ∀ p, (e p).Nonempty ∧ (e p).card ≤ 2) :
    ∃ q : Fin (Fintype.card Q) ≃ Q, ∀ j : ℕ, j ≤ Fintype.card Q →
      (j : ℤ) - ((Finset.univ.filter fun p => ∀ x ∈ e p, (q.symm x : ℕ) < j).card : ℤ) ≤
        max 0 ((Fintype.card Q : ℤ) - Fintype.card P) + 1 := by sorry

end GaussianSweep
