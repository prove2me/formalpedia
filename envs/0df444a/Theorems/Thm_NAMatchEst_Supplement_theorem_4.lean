-- Prove2me | Theorems.Thm_NAMatchEst_Supplement_theorem_4
-- name    : NAMatchEst.Supplement.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:39:14.597781+00:00
-- url     : https://prove2.me/theorems/bfece57a-57ae-42c8-ba95-4ac4b99958b9
-- title:
--   Theorem 4 — moment-matching lower bounds $\Omega(n/\alpha^{1/2+C_0/\sqrt{\log\alpha}})$ and $\Omega((n/\alpha)^{2-C_0/\sqrt{\log(n/\alpha)}})$
-- statement:
--   Here $\mu(G)$ is the maximum matching size of a graph $G$, and an estimate $\widehat\mu$ is an **$\alpha$-approximation** if $\mu(G)/\alpha\le\widehat\mu\le\mu(G)$. Logarithms are to base 2.
--
--   There are absolute constants $K_0>1$, $C_0>0$ and $c>0$ such that, for all sufficiently large $n$, the following holds for every real $\alpha$ in each of the two ranges below. There is a bipartition of the $n$ vertices, fixed before the algorithm, such that every randomized non-adaptive adjacency-list algorithm that outputs an $\alpha$-approximation with probability at least $2/3$ on every simple graph on these $n$ vertices whose edges all cross the bipartition and with $\mu(G)\ge1$ (under every ordering of the adjacency lists) makes, in the worst case, at least
--
--   $$
--   c\cdot\frac{n}{\alpha^{1/2+C_0/\sqrt{\log\alpha}}}\quad\text{distinct queries if } n^{1/2}\le\alpha\le n^{2/3},
--   \qquad
--   c\cdot\Big(\frac{n}{\alpha}\Big)^{2-C_0/\sqrt{\log(n/\alpha)}}\quad\text{if } n^{2/3}\le\alpha\le n/K_0 .
--   $$
--
--   Since an algorithm that succeeds on every $n$-vertex input succeeds on this restricted class, the same bounds hold for algorithms that succeed on all inputs.
--
--   When $\alpha\ge n^{2/3}$ and $n/\alpha\to\infty$ the bound is $(n/\alpha)^{2-o(1)}$, and in the middle range it is $n/\alpha^{1/2+o(1)}$; together with the paper's upper bounds this pins down the non-adaptive query complexity of matching-size estimation for $\alpha\ge n^{1/2}$ up to subpolynomial factors.
--
--   **Formalization Note** The worst case counts distinct queries on outcomes of positive probability (`DistinctCostLE`), and the bound holds for every worst-case bound $q$.
--
--   Differences from the source:
--   - encoding: a simple graph on n vertices with its adjacency lists in some order → G : AdjList n on Fin n (ordered, duplicate-free, symmetric, loopless lists); reason: every simple graph with every list ordering is an AdjList; same instances
--   - encoding: µ(G) → TuranMatching.Clique.matchingNumber G.toGraph; reason: the published matching number, the same quantity
--   - encoding: any randomized non-adaptive algorithm → every RandAlg (finite seed space); reason: at a fixed n the success probabilities on the finitely many inputs of any algorithm with a given worst-case query bound are a convex combination of those of deterministic algorithms, realized by a finite mixture with the same bound (Carathéodory); same theorem
--   - encoding: worst-case number of queries, identical queries answered once (p.20) → DistinctCostLE: distinct queries on every seed of positive probability, for every bound q; reason: the paper's cost measure
--   - reading: Ω(f) → c · f with c > 0 and a threshold N₀, chosen before n; reason: asymptotic notation
--   - reading: a specified bipartition → a bipartition side : Fin n → Bool, chosen after n and α and before the algorithm; success required only on graphs whose edges cross it and with µ(G) ≥ 1; reason: the bipartition is public information fixed before the algorithm, as in the hard instances of §4
-- source:
--   Khanna–Mukhopadhyay–Shah, Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), Theorem 4, p.32 (PDF 36)

import Mathlib
import Definitions.Def_TuranMatching_Clique_Setting
import Definitions.Def_NAMatchEst_AdjList
import Definitions.Def_NAMatchEst_AdjList_toGraph
import Definitions.Def_NAMatchEst_RandAlg
import Definitions.Def_NAMatchEst_RandAlg_prob
import Definitions.Def_NAMatchEst_Supplement_DistinctCostLE

namespace NAMatchEst.Supplement

/-- **Theorem 4.** There are absolute constants `K₀ > 1` and `C₀ > 0` with the following property.
Any randomized non-adaptive adjacency-list algorithm that obtains an `α`-approximation to maximum
matching size with probability at least `2/3` on every `n`-vertex input requires
`Ω(n / α^{1/2 + C₀/√log α})` queries for `n^{1/2} ⩽ α ⩽ n^{2/3}` and
`Ω((n/α)^{2 − C₀/√log(n/α)})` queries for `n^{2/3} ⩽ α ⩽ n/K₀`, in the worst case. Both statements
hold even for simple bipartite graphs with a specified bipartition and with `µ(G) ⩾ 1`.

Khanna–Mukhopadhyay–Shah, *Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation*, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), Theorem 4, p.32 (PDF 36).

**Formalization Note**
1. `K₀`, `C₀`, one constant `c` for both `Ω`'s and a threshold `N₀` ("for all sufficiently
   large `n`") are chosen first. For each `n`, `α` in a range, a bipartition `side` is fixed before
   the algorithm (the "specified bipartition"); every algorithm that succeeds on every simple graph
   on `Fin n` whose edges all cross `side` and whose matching number is at least one, under every
   adjacency-list ordering, needs the bound. The unrestricted statement follows, since an algorithm
   succeeding on every input succeeds on this class.
2. Queries are counted as distinct queries on seeds of positive probability (`DistinctCostLE`);
   the bound holds for every worst-case bound `q`.
3. `log` is base 2 (§2, p.13): `Real.logb 2`. `n` is the total number of vertices. -/
theorem theorem_4 : ∃ K₀ : ℝ, 1 < K₀ ∧ ∃ C₀ : ℝ, 0 < C₀ ∧ ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ,
    ∀ (n : ℕ) (α : ℝ), N₀ ≤ n →
      ((n : ℝ) ^ ((1 : ℝ) / 2) ≤ α → α ≤ (n : ℝ) ^ ((2 : ℝ) / 3) →
        ∃ side : Fin n → Bool, ∀ A : RandAlg n ℝ,
          (∀ G : AdjList n, (∀ u v, G.toGraph.Adj u v → side u ≠ side v) →
            1 ≤ TuranMatching.Clique.matchingNumber G.toGraph →
            2 / 3 ≤ A.prob G (fun muhat =>
              (TuranMatching.Clique.matchingNumber G.toGraph : ℝ) / α ≤ muhat ∧
                muhat ≤ (TuranMatching.Clique.matchingNumber G.toGraph : ℝ))) →
          ∀ q : ℝ, DistinctCostLE A q →
            c * ((n : ℝ) / α ^ ((1 : ℝ) / 2 + C₀ / Real.sqrt (Real.logb 2 α))) ≤ q) ∧
      ((n : ℝ) ^ ((2 : ℝ) / 3) ≤ α → α ≤ (n : ℝ) / K₀ →
        ∃ side : Fin n → Bool, ∀ A : RandAlg n ℝ,
          (∀ G : AdjList n, (∀ u v, G.toGraph.Adj u v → side u ≠ side v) →
            1 ≤ TuranMatching.Clique.matchingNumber G.toGraph →
            2 / 3 ≤ A.prob G (fun muhat =>
              (TuranMatching.Clique.matchingNumber G.toGraph : ℝ) / α ≤ muhat ∧
                muhat ≤ (TuranMatching.Clique.matchingNumber G.toGraph : ℝ))) →
          ∀ q : ℝ, DistinctCostLE A q →
            c * ((n : ℝ) / α) ^ ((2 : ℝ) - C₀ / Real.sqrt (Real.logb 2 ((n : ℝ) / α))) ≤ q) := by sorry

end NAMatchEst.Supplement
