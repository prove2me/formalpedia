-- Prove2me | Theorems.Thm_JohnsonApprox_SubsetSum_Supplement_theorem_5
-- name    : JohnsonApprox.SubsetSum.Supplement.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T02:26:37.281029+00:00
-- url     : https://prove2.me/theorems/cc46a5b1-fac7-4bbf-9987-8cb69227fd22
-- title:
--   Theorem 5 (corrected: lower bound false for k = 2, 3, 4) — greedy C1 on NC′(k) has ratio ≤ 2; ≥ (2k−1)/k for k = 1 and k ≥ 5
-- statement:
--   Let $k \ge 1$. Consider node cover on graphs in which every node is incident to exactly $k$ arcs, written as SET COVERING I: a finite family $S_i$ ($i \in \iota$) of arc sets in which every arc lies in exactly two of the $S_i$ and every $S_i$ has exactly $k$ arcs (the class $\mathrm{NC}'(k)$). Let $F^*$ be the least number of sets of the family covering every arc, and let algorithm C1 repeatedly choose a set covering the most still-uncovered arcs, ties broken arbitrarily, until all arcs are covered. Call a subfamily $F_1$ **choosable** if some sequence of admissible choices of C1 returns it.
--
--   The paper states: for all $k \ge 1$ and $n > 0$, $R[\mathrm{C1}, \mathrm{NC}'(k)](n) \le 2$, and for all sufficiently large $n$, $R[\mathrm{C1}, \mathrm{NC}'(k)](n) \ge (2k-1)/k$. The second clause is false for $k = 2, 3, 4$. This item states:
--
--   1. **Upper bound** (every $k \ge 1$). For every $\mathrm{NC}'(k)$ input and every choosable $F_1$,
--   $$|F_1| \le 2F^* .$$
--   2. **Lower bound as printed, for $k = 1$ and for every $k \ge 5$.** There is an $\mathrm{NC}'(k)$ input encoding a simple graph (no two nodes share more than one arc) with $F^* > 0$, and a choosable $F_1$, such that
--   $$k\,|F_1| \ge (2k-1)\,F^* .$$
--   3. **Correction for $k = 2, 3, 4$.** For every $\mathrm{NC}'(k)$ input and every choosable $F_1$,
--   $$3|F_1| \le 4F^* \ (k = 2), \qquad 2|F_1| \le 3F^* \ (k = 3), \qquad 15|F_1| \le 26F^* \ (k = 4).$$
--   Since $4/3 < 3/2$, $3/2 < 5/3$ and $26/15 < 7/4$, no input with $F^* > 0$ reaches the printed ratio $(2k-1)/k$ for these $k$.
--
--   The upper bound shows that on regular graphs greedy node cover is never worse than twice optimal, a better constant than the harmonic bound $\sum_{j=1}^k 1/j$ of Theorem 4 for $k \ge 4$. For $k = 1$ and $k \ge 5$, the stated lower bound and the upper bound bracket the worst-case ratio; for $k = 2, 3, 4$, clause 3 refutes the printed lower bound.
--
--   **Formalization Note** The size-indexed worst-case ratio $R[\mathrm{C1}, \mathrm{NC}'(k)](n)$ is replaced by its size-free equivalent (Section 2 of the paper): an upper bound for every input and every choosable output, and a lower bound "for all sufficiently large $n$" by one input with a choosable output (since $R(n)$ is a maximum over the finitely many inputs of size at most $n$, it is nondecreasing). Ratios are cleared of denominators, with $(2k-1)$ computed in $\mathbb{Q}$. The family, $F^*$ (`opt`) and C1 (`Choosable`) are the published `JohnsonApprox.SetCover` definitions; $\mathrm{NC}'(k)$ and the simple-graph condition are `InNCPrime k` and `NoParallelArcs`.
--
--   Differences from the source:
--   - correction: R[C1, NC′(k)](n) ≥ (2k − 1)/k for all sufficiently large n, for every k ≥ 1 → the printed bound for k = 1 and k ≥ 5, and 3|F₁| ≤ 4F*, 2|F₁| ≤ 3F*, 15|F₁| ≤ 26F* for every input and choosable F₁ when k = 2, 3, 4; reason: the paper gives no proof of the lower bound, and a counting argument (C1's first-phase picks dominate the graph, its last-phase picks each leave a node unpicked, F* ≥ |T|/k) shows the worst ratio is at most 4/3, 3/2, 26/15 < (2k − 1)/k (DISPROOF.md); cycles C_6 with ratio 4/3 show the k = 2 bound is attained.
--   - encoding: R[C1, NC′(k)](n) indexed by an unspecified input size n → for all inputs and all choosable outputs (upper bounds), one input with a choosable output and F* > 0 (lower bound); reason: the series' size-free restatement of Section 2; R(n) is a nondecreasing maximum over finitely many inputs.
--   - encoding: a graph G = (N, A) with node covers N′ and m(N′) = |N′| → an indexed family S : ι → Finset α with every point in exactly two indices, F* = opt S, and a lower-bound witness satisfying NoParallelArcs; reason: the paper's own equivalence of NC with this restriction of SC (p. 269); the no-parallel-arcs condition makes the witness a simple graph.
--   - generalization: graphs → every NC′(k) family, including those with parallel arcs, in the upper bound and the k = 2, 3, 4 bounds; reason: these clauses quantify universally, so they specialize to simple graphs.
-- source:
--   Johnson, Approximation algorithms for combinatorial problems, J. Comput. System Sci. 9 (1974), p. 269, Theorem 5 (with the remark after it); NC′(k) defined on p. 269, Section 5; C1 on p. 265

import Mathlib
import Definitions.Def_JohnsonApprox_SetCover_Problem
import Definitions.Def_JohnsonApprox_SetCover_C1
import Definitions.Def_JohnsonApprox_SubsetSum_Supplement_NCPrime

namespace JohnsonApprox.SubsetSum.Supplement

open JohnsonApprox.SetCover

theorem theorem_5 (k : ℕ) (hk : 1 ≤ k) :
    -- (a) upper bound: R[C1, NC′(k)](n) ≤ 2
    (∀ {ι α : Type} [Fintype ι] [DecidableEq α] (S : ι → Finset α), InNCPrime k S →
        ∀ F₁ : Finset (Finset α), Choosable S F₁ → F₁.card ≤ 2 * opt S) ∧
    -- (b), (d) the printed lower bound (2k − 1)/k, for k = 1 and for every k ≥ 5
    ((k = 1 ∨ 5 ≤ k) →
      ∃ (ι α : Type) (_ : Fintype ι) (_ : DecidableEq α) (S : ι → Finset α),
        InNCPrime k S ∧ NoParallelArcs S ∧
        ∃ F₁ : Finset (Finset α), Choosable S F₁ ∧ 0 < opt S ∧
          ((2 : ℚ) * k - 1) * opt S ≤ k * F₁.card) ∧
    -- (c) correction for k = 2, 3, 4: ratios at most 4/3, 3/2, 26/15 < (2k − 1)/k
    (k = 2 → ∀ {ι α : Type} [Fintype ι] [DecidableEq α] (S : ι → Finset α), InNCPrime k S →
        ∀ F₁ : Finset (Finset α), Choosable S F₁ → 3 * F₁.card ≤ 4 * opt S) ∧
    (k = 3 → ∀ {ι α : Type} [Fintype ι] [DecidableEq α] (S : ι → Finset α), InNCPrime k S →
        ∀ F₁ : Finset (Finset α), Choosable S F₁ → 2 * F₁.card ≤ 3 * opt S) ∧
    (k = 4 → ∀ {ι α : Type} [Fintype ι] [DecidableEq α] (S : ι → Finset α), InNCPrime k S →
        ∀ F₁ : Finset (Finset α), Choosable S F₁ → 15 * F₁.card ≤ 26 * opt S) := by sorry

end JohnsonApprox.SubsetSum.Supplement
