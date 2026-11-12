-- Prove2me | Theorems.Thm_MatroidEquitability_theorem_1
-- name    : MatroidEquitability.theorem_1
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T06:32:19.351161+00:00
-- url     : https://prove2.me/theorems/870c417a-a59c-4465-96fc-f1f7f3a809b6
-- title:
--   Theorem 1 — weighted matroid equitability, with (1) and (2)
-- statement:
--   Let $M=(E,\mathcal I)$ be a finite matroid whose ground set can be partitioned into $k$ bases, and let $w\in\mathbb R^E_{\ge 0}$. Then $E$ has a partition $E=B_1\sqcup\dots\sqcup B_k$ into bases such that
--
--   $$
--   |w(B_i)-w(B_j)|\le\max_{e\in E}w_e\qquad\text{for all }i,j\in[k], \tag{1}
--   $$
--
--   and, consequently,
--
--   $$
--   \Bigl|w(B_i)-\frac{w(E)}{k}\Bigr|\le\Bigl(1-\frac1k\Bigr)\cdot\max_{e\in E}w_e\qquad\text{for all }i\in[k]. \tag{2}
--   $$
--
--   This is the weighted matroid equitability theorem. The case $w=\mathbf 1_S$ is the matroid equitability conjecture of Fekete and Szabó, proved by Akrami, Liu, Raj and Végh.
--
--   **Formalization Note** Clauses (1) and (2) are asserted for one and the same partition. Division is in $\mathbb R$.
--
--   Differences from the source:
--   - encoding: a matroid, with weights summed over sets and maxima over $E$, never called finite on the page → `Matroid α` with `[M.Finite]`, sums as `finsum`; reason: the sums, $\max_{e\in E}$ and "finitely many partitions" all presuppose a finite ground set; the same instances
--   - generalization: $k$ a positive integer (§1.3 fixes $[k]$ for positive $k$) → `k : ℕ`, including $k=0$, where $E=\emptyset$ and there is no index $i$; reason: the case $k\ge 1$ is the source's statement; at $k=0$ both clauses are empty
-- source:
--   Bérczi, Liu, Reis, Tarnawski, Weighted Equitability and Matroid-Constrained Discrepancy, arXiv:2608.13983 (held version sha256 0675891a…), Theorem 1 with (1) and (2), pp.1–2 (PDF pp.3–4)

import Mathlib
import Definitions.Def_MatroidEquitability_setWeight
import Definitions.Def_MatroidEquitability_maxWeight
import Definitions.Def_MatroidEquitability_IsBasePartition

namespace MatroidEquitability

/-- Theorem 1 (weighted matroid equitability): if the ground set of a matroid `M` can be partitioned
into `k` bases and `w ≥ 0` on `E`, there is a partition `E = B₁ ⊔ ⋯ ⊔ B_k` into bases with
`|w(B_i) − w(B_j)| ≤ max_{e∈E} w_e` for all `i, j` (1), and with
`|w(B_i) − w(E)/k| ≤ (1 − 1/k) · max_{e∈E} w_e` for all `i` (2) (printed pp.1–2 = PDF pp.3–4 of
Bérczi, Liu, Reis, Tarnawski, *Weighted Equitability and Matroid-Constrained Discrepancy*, arXiv:2608.13983 (held version sha256 0675891a…)).

**Formalization Note.** `[M.Finite]` encodes the paper's finite matroids. Clauses (1) and (2) hold for
one and the same partition. Division is in `ℝ`; at `k = 0` there is no index and both clauses are
empty. -/
theorem theorem_1 {α : Type*} (M : Matroid α) [M.Finite] (k : ℕ) (w : α → ℝ)
    (hw : ∀ e ∈ M.E, 0 ≤ w e) (hpart : ∃ B₀ : Fin k → Set α, IsBasePartition M B₀) :
    ∃ B : Fin k → Set α, IsBasePartition M B ∧
      (∀ i j, |setWeight w (B i) - setWeight w (B j)| ≤ maxWeight M w) ∧
      ∀ i, |setWeight w (B i) - setWeight w M.E / k| ≤ (1 - 1 / (k : ℝ)) * maxWeight M w := by sorry

end MatroidEquitability
