-- Prove2me | Theorems.Thm_MSTCuts2027_Parallel_parallel_all_pairs_mincuts
-- name    : MSTCuts2027.Parallel.parallel_all_pairs_mincuts
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:51:34.88435+00:00
-- url     : https://prove2.me/theorems/5ab9ddd2-8694-4145-96ea-c264eeba5d90
-- title:
--   Theorem 3 — parallel all-pairs mincuts for arbitrary symmetric cut functions
-- statement:
--   There are one program $A$ of the machine and constants $c_D,c_W,k$ such that the following holds for every $n$. Let $V=\{0,\dots,n-1\}$, let $F$ be any symmetric real-valued function on the cuts of $V$, let $P$ be a correct single-pair mincut procedure for $F$, and let $D_P,W_P$ bound the depth and work of its queries. Then $A$, with word size $(n+2)^k$, halts on the initial memory (only $n$ is stored), and it stores, for every ordered pair of distinct vertices $u,v$, a pointer to a Boolean array that is a $(u,v)$-mincut, together with the value $\lambda_1(u,v)$. If $n\ge2$, then
--   $$\text{depth}\le c_D\bigl(\lceil\log_2 n\rceil\,D_P+\lceil\log_2 n\rceil^2\bigr),\qquad \text{work}\le c_W\bigl(n\lceil\log_2 n\rceil\,W_P+n^2\bigr).$$
--
--   The program learns about $F$ only through $P$, so querying all pairs would cost $\binom n2W_P$ work, and a sequential merging algorithm would cost depth linear in $n$. The theorem matches the best of these two extremes up to a logarithmic factor.
--
--   **Formalization Note** The program is one finite term, fixed before $n$, and reads $n$ from memory; costs come from the machine's semantics. The cut output is the stored cover plus the pointer table, as in Appendix E.
--
--   Differences from the source:
--   - encoding: a graph G = (V, E) on n vertices with cut values given by F → the vertex set Fin n and the function F, without E; reason: the values of cuts are given by F, so E plays no role; every (G, F) gives such an instance
--   - encoding: a parallel algorithm (CREW PRAM, Appendix E) → a Program of the fork-join machine, with word size (n+2)^k, in which concurrent threads may not write a location another reads or writes; reason: a run of this stricter model is an exclusive-write execution; a word has O(log n) bits, the standard PRAM word
--   - encoding: P computes an (s, t)-mincut, with depth DP(s, t) and work WP(s, t) → an external procedure answering all distinct pairs correctly, with any common bounds DP, WP on the costs it reports; reason: the source uses one depth and one work figure for all queried pairs; a query charges the reported costs
--   - encoding: computes all-pairs mincuts → a pointer to a Boolean array and the mincut value, for every ordered pair of distinct vertices; reason: Appendix E: the output is the cover C with the matrix M; pairs u = v have no mincut
--   - encoding: O(·) depth and work → constants fixed before the instance, for n ≥ 2, with ⌈log₂ n⌉; reason: the bounds are not meaningful for n ≤ 1, where A still has to halt, with a vacuously correct output
-- source:
--   Baswana–Roy, Using MSTs to Compute All-Pairs Mincuts and Beyond ..., STOC 2027 submission #21, pinned preprint SHA-256 faa337be0f0f1bfbbcf924cb3591bd51ded2a6ef2c9e2154e00534a840156a11, Theorem 3, printed p. 3, PDF p. 5

import Mathlib
import Definitions.Def_FlowsNetworks_MultiTerminal_SpanningSubtree
import Definitions.Def_MSTCuts2027_Parallel_CutModel
import Definitions.Def_MSTCuts2027_Parallel_Machine
import Definitions.Def_MSTCuts2027_Parallel_Algorithms

namespace MSTCuts2027.Parallel

/-- Theorem 3 (Parallel All-Pairs Mincuts): one fixed program, with constants fixed before the input,
computes a mincut pointer and value for every pair of distinct vertices of any `n`-vertex instance
with arbitrary symmetric real `F`, in depth `O(log n · D_P + log² n)` and work
`O(n log n · W_P + n²)`, where `D_P` and `W_P` bound the costs of the single-pair procedure `P`. -/
theorem parallel_all_pairs_mincuts :
    ∃ (A : Program) (entry cD cW k : ℕ), ∀ (n : ℕ) (F : Finset (Fin n) → ℝ),
      IsSymmetricCutFunction F →
      ∀ P : Oracle ℝ n, IsMincutOracle F P →
      ∀ DP WP : ℕ, (∀ u v : Fin n, u ≠ v → (P u v).depth ≤ DP ∧ (P u v).work ≤ WP) →
        ∃ o : Outcome ℝ,
          Halts (⟨(n + 2) ^ k, P⟩ : Machine ℝ n) A entry [] (initialStore ℝ n) o ∧
          AllPairsOutput F o.store ∧
          (2 ≤ n →
            o.depth ≤ cD * (Nat.clog 2 n * DP + (Nat.clog 2 n) ^ 2) ∧
            o.work ≤ cW * (n * Nat.clog 2 n * WP + n ^ 2)) := by sorry

end MSTCuts2027.Parallel
