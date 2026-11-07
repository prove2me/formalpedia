-- Prove2me | Theorems.Thm_LocalBreadth_lemma_5_12
-- name    : LocalBreadth.lemma_5_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:56:55.516617+00:00
-- url     : https://prove2.me/theorems/d4553a7c-47f7-4b9b-8914-e8cb6c9e4b43
-- title:
--   Lemma 5.12 — compatible boards, with their constants
-- statement:
--   This is the root step and the child step of the board construction, for arbitrary sets.
--
--   1. If $L\subseteq\mathbb Z$ is infinite and $N\ge1$, there is a partition of $\mathbb Z$ into consecutive intervals with exactly $N$ points of $L$ in each. So at a root one may take $B_v=N_v$.
--   2. If $L\subseteq L'$, $L$ is infinite, $N\ge1$, and $\mathbb Z$ is partitioned into consecutive intervals with at most $B'$ points of $L'$ in each, then there is a partition into unions of these intervals with
--   $$N\le|L\cap I|\le N+B'-1$$
--   for every class $I$. So at a child of $u$ one may take $B_v=N_v+B_u-1$.
--
--   A class may be unbounded as an interval of integers, but its trace on $L$ is finite.
--
--   Differences from the source:
--   - generalization: the partitions at the vertices $v$ of the forest, with parent $u$ → the two steps of the recursion for arbitrary sets $L\subseteq L'$; reason: with $L=L_v$, $L'=L_u$ the statement gives the lemma by the page's induction on the vertex order, including equal labels (§5.8.6)
-- source:
--   Kleinberg, Wei, Characterizing Local Breadth in Language Generation, STOC 2027 submission (manuscript sha256 f924cbfc…), Lemma 5.12, p.31; §5.8.6, p.40

import Mathlib
import Definitions.Def_LocalBreadth_ProtectedForest

namespace LocalBreadth

/-- Lemma 5.12 (compatible boards). Kleinberg, Wei, STOC 2027 submission (manuscript sha256 f924cbfc…),
p.31, with §5.8.6, p.40, in the abstract form its proof gives. (a) The root step: an infinite `L` and
`N ≥ 1` admit a partition of `ℤ` into consecutive intervals with exactly `N` points of `L` in each, so
`B_v = N_v`. (b) The child step: if `L ⊆ L'`, `L` is infinite, `N ≥ 1`, and `J` is such a partition with at
most `B'` points of `L'` in each class, then some coarsening of `J` has between `N` and `N + B' − 1` points of
`L` in each class, so `B_v = N_v + B_u − 1`. -/
theorem lemma_5_12 :
    (∀ (L : Set ℤ) (N : ℕ), L.Infinite → 1 ≤ N →
      ∃ I : ℤ → Set ℤ, IsBoardPartition I ∧ ∀ x, (L ∩ I x).Finite ∧ (L ∩ I x).ncard = N) ∧
    (∀ (L L' : Set ℤ) (N B' : ℕ) (J : ℤ → Set ℤ), L.Infinite → L ⊆ L' → 1 ≤ N →
      IsBoardPartition J → (∀ x, (L' ∩ J x).Finite ∧ (L' ∩ J x).ncard ≤ B') →
      ∃ I : ℤ → Set ℤ, IsBoardPartition I ∧ (∀ x, J x ⊆ I x) ∧
        ∀ x, (L ∩ I x).Finite ∧ N ≤ (L ∩ I x).ncard ∧ (L ∩ I x).ncard ≤ N + B' - 1) := by sorry

end LocalBreadth
