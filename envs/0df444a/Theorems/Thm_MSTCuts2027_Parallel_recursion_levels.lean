-- Prove2me | Theorems.Thm_MSTCuts2027_Parallel_recursion_levels
-- name    : MSTCuts2027.Parallel.recursion_levels
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:51:31.274451+00:00
-- url     : https://prove2.me/theorems/c4856047-446d-437e-b643-440c49b39e14
-- title:
--   Lemma 16 — disjoint subproblems and logarithmically many levels in Algorithm 4
-- statement:
--   There is a constant $c$ such that for every $n$:
--
--   1. the blocks of Algorithm 4 at any one recursion level are pairwise disjoint;
--   2. if $n\ge2$, every nonempty recursion level $k$ satisfies $k\le c\lceil\log_2 n\rceil$.
--
--   Here the recursion starts from the block $\{0,\dots,n-1\}$, and a block with more than two elements splits into consecutive parts of sizes $\lfloor s/2\rfloor$ and $\lceil s/2\rceil$.
--
--   Differences from the source:
--   - encoding: the subset of vertices of a subproblem → blocks of consecutive positions of ord, computed by subproblemLevel using the split of subsetBody; reason: mainBody fills ord with the identity, so positions are vertices
--   - encoding: O(log n) recursion levels → k ≤ c⌈log₂ n⌉ for n ≥ 2; reason: for n ≤ 1 there is one level and the logarithm is 0
-- source:
--   Baswana–Roy, Using MSTs to Compute All-Pairs Mincuts and Beyond ..., STOC 2027 submission #21, pinned preprint SHA-256 faa337be0f0f1bfbbcf924cb3591bd51ded2a6ef2c9e2154e00534a840156a11, Lemma 16, printed p. 25, PDF p. 27

import Mathlib
import Definitions.Def_FlowsNetworks_MultiTerminal_SpanningSubtree
import Definitions.Def_MSTCuts2027_Parallel_CutModel
import Definitions.Def_MSTCuts2027_Parallel_Machine
import Definitions.Def_MSTCuts2027_Parallel_Algorithms

namespace MSTCuts2027.Parallel

/-- Lemma 16: subproblems at one recursion level of Algorithm 4 are disjoint, and there are
`O(log n)` levels. -/
theorem recursion_levels :
    ∃ c : ℕ, ∀ n : ℕ,
      (∀ k, (subproblemLevel n k).Pairwise fun p q =>
        Disjoint (Finset.Ico p.1 p.2) (Finset.Ico q.1 q.2)) ∧
      (2 ≤ n → ∀ k, subproblemLevel n k ≠ [] → k ≤ c * Nat.clog 2 n) := by sorry

end MSTCuts2027.Parallel
