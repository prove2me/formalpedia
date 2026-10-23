-- Prove2me | Theorems.Thm_JohnsonApprox1974_thm5_nodeCover_regular_faithful
-- name    : JohnsonApprox1974.thm5_nodeCover_regular_faithful
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-10-23T01:28:10.604852+00:00
-- url     : https://prove2.me/theorems/7f2f4519-c1b1-49fc-a8ee-a360552e8b9b
-- title:
--   Theorem 5 — greedy C1 on node cover of $k$-regular graphs
-- statement:
--   Let $k \ge 1$. A finite simple $k$-regular graph $G = (N, A)$ is encoded as a set-covering input: the points are the arcs, and each node $v \in N$ gives the set $S_v$ of the $k$ arcs at $v$. So every set has exactly $k$ points, every point lies in exactly two sets $S_u, S_v$ ($u \ne v$), and no two points lie in the same two sets. A subcover is a node cover, $F^*$ is the minimum size of a node cover, and C1 is the greedy set-cover algorithm (repeatedly choose a set covering the most uncovered points, ties broken arbitrarily). Then:
--
--   1. for every such input and every family $F_1$ choosable by C1,
--   $$|F_1| \le 2\, F^*;$$
--   2. there are such an input and a choosable $F_1$ with $F^* > 0$ and
--   $$|F_1| \ge \frac{2k-1}{k}\, F^*.$$
--
--   This is Theorem 5 of Johnson (1974), "For all $k \ge 1$ and $n > 0$, $R[C1, NC'(k)](n) \le 2$, and for all sufficiently large $n$, $R[C1, NC'(k)](n) \ge (2k-1)/k$", in size-free form: since $R$ is a maximum over finitely many inputs and nondecreasing in $n$, the first clause is part 1 and the second is part 2. It complements Theorem 4, whose bound $\sum_{j=1}^k 1/j$ is weaker than $2$ for $k \ge 4$.
--
--   **Formalization Note** Inputs use the indexed families of the set-covering mission; the encoding conditions are stated on the family. Ratios are multiplied out in $\mathbb N$ ($2k - 1$ does not truncate since $k \ge 1$).
-- source:
--   Johnson, Approximation algorithms for combinatorial problems, J. Comput. System Sci. 9 (1974) 256–278, doi:10.1016/S0022-0000(74)80044-9, p. 269, Theorem 5

import Mathlib
import Definitions.Def_JohnsonApprox_SetCover_Problem
import Definitions.Def_JohnsonApprox_SetCover_C1

open JohnsonApprox.SetCover

theorem JohnsonApprox1974.thm5_nodeCover_regular_faithful (k : ℕ) (hk : 1 ≤ k) :
    (∀ {ι α : Type} [Fintype ι] [DecidableEq α] (S : ι → Finset α),
        (∀ i, (S i).card = k) →
        (∀ x ∈ ground S, (Finset.univ.filter (fun i => x ∈ S i)).card = 2) →
        (∀ x ∈ ground S, ∀ y ∈ ground S, (∀ i, x ∈ S i ↔ y ∈ S i) → x = y) →
        ∀ F₁ : Finset (Finset α), Choosable S F₁ → F₁.card ≤ 2 * opt S) ∧
      (∃ (ι α : Type) (_ : Fintype ι) (_ : DecidableEq α) (S : ι → Finset α),
        (∀ i, (S i).card = k) ∧
        (∀ x ∈ ground S, (Finset.univ.filter (fun i => x ∈ S i)).card = 2) ∧
        (∀ x ∈ ground S, ∀ y ∈ ground S, (∀ i, x ∈ S i ↔ y ∈ S i) → x = y) ∧
        ∃ F₁ : Finset (Finset α), Choosable S F₁ ∧ 0 < opt S ∧
          (2 * k - 1) * opt S ≤ k * F₁.card) := by sorry
