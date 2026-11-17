-- Prove2me | Theorems.Thm_NAMatchEst_Supplement_theorem_13
-- name    : NAMatchEst.Supplement.theorem_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:46:07.669404+00:00
-- url     : https://prove2.me/theorems/3519ab29-cf36-499a-8954-3bd79af12ab5
-- title:
--   Theorem 13 — $(n^{3/4}/10)$-approximation needs $\Omega(n^{3/8+1/24}/\log^5 n)$ non-adaptive queries
-- statement:
--   Here $\mu(G)$ is the maximum matching size; logarithms are to base 2.
--
--   There are $c>0$ and $N_0$ such that for every $n\ge N_0$ the following holds. Every randomized non-adaptive adjacency-list algorithm that, on every simple graph $G$ on $n$ vertices and every ordering of its adjacency lists, outputs $\widehat\mu$ with
--
--   $$
--   \frac{\mu(G)}{n^{3/4}/10}\le\widehat\mu\le\mu(G)
--   $$
--
--   with probability at least $2/3$ makes, in the worst case, at least
--
--   $$
--   c\cdot\frac{n^{3/8+1/24}}{\log^5 n}
--   $$
--
--   distinct queries.
--
--   This was the paper's first lower bound beyond the $(n/\alpha)^{3/2}$ tradeoff at $\alpha=n^{3/4}$; Theorem 4 supersedes it.
--
--   Differences from the source:
--   - encoding: a simple graph on n vertices with its adjacency lists in some order → G : AdjList n on Fin n (ordered, duplicate-free, symmetric, loopless lists); reason: every simple graph with every list ordering is an AdjList; same instances
--   - encoding: µ(G) → TuranMatching.Clique.matchingNumber G.toGraph; reason: the published matching number, the same quantity
--   - encoding: any randomized non-adaptive algorithm → every RandAlg (finite seed space); reason: at a fixed n the success probabilities on the finitely many inputs of any algorithm with a given worst-case query bound are a convex combination of those of deterministic algorithms, realized by a finite mixture with the same bound (Carathéodory); same theorem
--   - encoding: worst-case number of queries, identical queries answered once (p.20) → DistinctCostLE: distinct queries on every seed of positive probability, for every bound q; reason: the paper's cost measure
--   - reading: Ω(f) → c · f with c > 0 and a threshold N₀, chosen before n; reason: asymptotic notation
-- source:
--   Khanna–Mukhopadhyay–Shah, Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), Theorem 13, p.154 (PDF 158)

import Mathlib
import Definitions.Def_TuranMatching_Clique_Setting
import Definitions.Def_NAMatchEst_AdjList
import Definitions.Def_NAMatchEst_AdjList_toGraph
import Definitions.Def_NAMatchEst_RandAlg
import Definitions.Def_NAMatchEst_RandAlg_prob
import Definitions.Def_NAMatchEst_Supplement_DistinctCostLE

namespace NAMatchEst.Supplement

/-- **Theorem 13.** Any randomized algorithm that is given access to an arbitrary `n`-vertex graph
using non-adaptive adjacency list queries and can obtain an `(n^{3/4}/10)`-approximation to the
maximum matching size with probability at least `2/3` needs to use `Ω(n^{3/8+1/24}/log⁵ n)` queries.

Khanna–Mukhopadhyay–Shah, *Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation*, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), Theorem 13, p.154 (PDF 158).

**Formalization Note**
1. `Ω`: one constant `c > 0` and a threshold `N₀`; `log` base 2 (§2, p.13).
2. The algorithm must succeed with probability `⩾ 2/3` on every simple graph on `Fin n` under
   every adjacency-list ordering (the printed "arbitrary `n`-vertex graph"), with
   `µ(G)/α ⩽ µ̂ ⩽ µ(G)` for `α = n^{3/4}/10`.
3. Queries are counted as distinct queries on seeds of positive probability (`DistinctCostLE`). -/
theorem theorem_13 : ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ A : RandAlg n ℝ,
    (∀ G : AdjList n, 2 / 3 ≤ A.prob G (fun muhat =>
      (TuranMatching.Clique.matchingNumber G.toGraph : ℝ) / ((n : ℝ) ^ ((3 : ℝ) / 4) / 10) ≤
          muhat ∧
        muhat ≤ (TuranMatching.Clique.matchingNumber G.toGraph : ℝ))) →
    ∀ q : ℝ, DistinctCostLE A q →
      c * ((n : ℝ) ^ ((3 : ℝ) / 8 + 1 / 24) / Real.logb 2 n ^ 5) ≤ q := by sorry

end NAMatchEst.Supplement
