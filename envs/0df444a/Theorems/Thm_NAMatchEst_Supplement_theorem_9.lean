-- Prove2me | Theorems.Thm_NAMatchEst_Supplement_theorem_9
-- name    : NAMatchEst.Supplement.theorem_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:43:08.317333+00:00
-- url     : https://prove2.me/theorems/3fc5bbe1-fa8f-4ba0-b37d-618e5d9e399c
-- title:
--   Theorem 9 — superlinear lower bounds $\tilde\Omega((n/\alpha)^{3/2})$, $\Omega_r(n^{2-1/(r+1)}/\alpha^{3r-3+4/(r+1)})$, and $\Theta(n^2)$ for exact estimation
-- statement:
--   Here $\mu(G)$ is the maximum matching size and an estimate $\widehat\mu$ is an **$\alpha$-approximation** if $\mu(G)/\alpha\le\widehat\mu\le\mu(G)$. Logarithms are to base 2. All lower bounds concern randomized non-adaptive adjacency-list algorithms and count distinct queries in the worst case.
--
--   1. **(i)** There are $c>0$, $e\in\mathbb N$ and $N_0$ such that for all $n\ge N_0$ and $1\le\alpha\le n^{1/3}$, every algorithm returning an $\alpha$-approximation with probability at least $2/3$ on every simple $n$-vertex graph makes at least $c\,(n/\alpha)^{3/2}/\log^e n$ queries.
--   2. **(ii)** For every integer $r\ge2$ there are constants $C_r>0$ and $c_r>0$, depending only on $r$, such that whenever $1\le\alpha\le n^{1/3}$ and $n\ge C_r\alpha^{2r^2+1}$, there are a bipartition of the $n$ vertices and a set of isolated vertices, fixed before the algorithm, such that every algorithm returning an $\alpha$-approximation with probability at least $2/3$ on every simple graph whose edges cross the bipartition and whose designated vertices are isolated makes at least
--   $$
--   c_r\cdot\frac{n^{2-1/(r+1)}}{\alpha^{3r-3+4/(r+1)}}
--   $$
--   queries. In particular the bound holds for algorithms that succeed on all $n$-vertex graphs.
--   3. **(iii)** Exact estimation has query complexity $\Theta(n^2)$: there are $c>0$ and $N_0$ such that every algorithm outputting $\mu(G)$ with probability at least $2/3$ on every $n$-vertex graph, $n\ge N_0$, makes at least $c\,n^2$ queries; and there is $D$ such that for every $n$ some algorithm makes at most $D\,n^2$ queries on every outcome and outputs $\mu(G)$ with probability at least $2/3$ on every graph.
--
--   For subpolynomial $\alpha$, (ii) gives $n^{2-o(1)}$, so near-exact estimation requires essentially reading the whole graph.
--
--   **Formalization Note** In (ii) the algorithm may depend on the bipartition and the isolated set; the paper's further public datum, the core/dummy partition, places no restriction on the inputs and is subsumed by choosing the algorithm after the public data. The upper bound in (iii) counts every query on every seed.
--
--   Differences from the source:
--   - encoding: a simple graph on n vertices with its adjacency lists in some order → G : AdjList n on Fin n (ordered, duplicate-free, symmetric, loopless lists); reason: every simple graph with every list ordering is an AdjList; same instances
--   - encoding: µ(G) → TuranMatching.Clique.matchingNumber G.toGraph; reason: the published matching number, the same quantity
--   - encoding: any randomized non-adaptive algorithm → every RandAlg (finite seed space); reason: at a fixed n the success probabilities on the finitely many inputs of any algorithm with a given worst-case query bound are a convex combination of those of deterministic algorithms, realized by a finite mixture with the same bound (Carathéodory); same theorem
--   - encoding: worst-case number of queries, identical queries answered once (p.20) → DistinctCostLE: distinct queries on every seed of positive probability, for every bound q; reason: the paper's cost measure
--   - reading: Ω(f) → c · f with c > 0 and a threshold N₀, chosen before n; reason: asymptotic notation
--   - reading: Ω̃((n/α)^{3/2}) → c · (n/α)^{3/2} / (log₂ n)^e with c, e, N₀ chosen before n and α; reason: the uniform reading of Ω̃
--   - reading: given the bipartition, the isolated vertices and the core/dummy partition → ∃ side, ∃ iso fixed before the algorithm; success required on graphs crossing side with iso isolated; the core/dummy partition is not a separate datum; reason: the public data restrict the class only through the bipartition and the isolated vertices; any further public datum is information the algorithm, chosen afterwards, may already use
--   - reading: Θ(n²) query complexity of exact estimation → a lower bound c n² for n ≥ N₀ and an upper bound D n² (an algorithm with CostLE) for every n; reason: both halves of Θ
--   - generalization: there is a randomized non-adaptive algorithm → there is a RandAlg (finite seed space with real weights, queries a function of the seed); reason: a RandAlg is a randomized non-adaptive algorithm, so the Lean statement implies the source's
--   - generalization: worst-case number of queries, identical queries answered once (p.20) → CostLE: the query list on every seed, every repetition charged; reason: a bound on the charged count on every seed implies the source's bound
-- source:
--   Khanna–Mukhopadhyay–Shah, Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), Theorem 9, p.91 (PDF 95); proofs of (ii) and (iii), pp.115–118 (PDF 119–122)

import Mathlib
import Definitions.Def_TuranMatching_Clique_Setting
import Definitions.Def_NAMatchEst_AdjList
import Definitions.Def_NAMatchEst_AdjList_toGraph
import Definitions.Def_NAMatchEst_RandAlg
import Definitions.Def_NAMatchEst_RandAlg_prob
import Definitions.Def_NAMatchEst_RandAlg_CostLE
import Definitions.Def_NAMatchEst_Supplement_DistinctCostLE

namespace NAMatchEst.Supplement

/-- **Theorem 9.** For `1 ⩽ α ⩽ n^{1/3}`, the following worst-case query bounds hold for
non-adaptive adjacency-list algorithms that return an `α`-approximation to `µ(G)` with probability
at least `2/3` on every `n`-vertex simple graph.
(i) `Ω̃((n/α)^{3/2})` queries are necessary.
(ii) For every fixed integer `r ⩾ 2`, there is a constant `C_r > 0` such that, whenever
`n ⩾ C_r α^{2r²+1}`, every such algorithm requires `Ω_r(n^{2−1/(r+1)} / α^{3r−3+4/(r+1)})` queries.
(iii) The query complexity of exact estimation is `Θ(n²)`.
The implicit constant in `Ω_r` depends only on `r`. Assertion (ii) holds for bipartite graphs even
when, before choosing its queries, the algorithm is given the bipartition, the isolated vertices,
and the partition of the remaining vertices into core and dummy vertices.

Khanna–Mukhopadhyay–Shah, *Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation*, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), Theorem 9, p.91 (PDF 95); proofs of (ii) and (iii), pp.115–118 (PDF 119–122).

**Formalization Note**
1. (i): one constant `c > 0`, one polylog exponent `e` and a threshold `N₀`, uniform over
   `1 ⩽ α ⩽ n^{1/3}`; `log` base 2.
2. (ii): for each `r ⩾ 2` the constants `C_r`, `c_r` depend only on `r`. The public information is
   a bipartition `side` and a set `iso` of isolated vertices fixed before the algorithm; the
   algorithm need only succeed on simple graphs whose edges cross `side` and in which every vertex of
   `iso` is isolated. The core/dummy partition of the remaining vertices is further public data the
   algorithm may depend on; it does not restrict the input class, so it is subsumed by the algorithm
   being chosen after `side` and `iso`. The unrestricted form follows.
3. (iii): exact estimation outputs `µ(G)` with probability `⩾ 2/3` on every graph; `Θ(n²)` is a
   lower bound `c n²` (for `n ⩾ N₀`) and an upper bound `D n²` (some algorithm, every `n`).
4. Lower bounds count distinct queries on seeds of positive probability (`DistinctCostLE`); the
   upper bound of (iii) counts every query on every seed (`CostLE`). -/
theorem theorem_9 :
    (∃ c : ℝ, 0 < c ∧ ∃ e : ℕ, ∃ N₀ : ℕ, ∀ (n : ℕ) (α : ℝ), N₀ ≤ n →
      1 ≤ α → α ≤ (n : ℝ) ^ ((1 : ℝ) / 3) → ∀ A : RandAlg n ℝ,
        (∀ G : AdjList n, 2 / 3 ≤ A.prob G (fun muhat =>
          (TuranMatching.Clique.matchingNumber G.toGraph : ℝ) / α ≤ muhat ∧
            muhat ≤ (TuranMatching.Clique.matchingNumber G.toGraph : ℝ))) →
        ∀ q : ℝ, DistinctCostLE A q →
          c * ((n : ℝ) / α) ^ ((3 : ℝ) / 2) / Real.logb 2 n ^ e ≤ q) ∧
    (∀ r : ℕ, 2 ≤ r → ∃ Cr : ℝ, 0 < Cr ∧ ∃ cr : ℝ, 0 < cr ∧ ∀ (n : ℕ) (α : ℝ),
      1 ≤ α → α ≤ (n : ℝ) ^ ((1 : ℝ) / 3) → Cr * α ^ (2 * r ^ 2 + 1) ≤ n →
      ∃ side : Fin n → Bool, ∃ iso : Finset (Fin n), ∀ A : RandAlg n ℝ,
        (∀ G : AdjList n, (∀ u v, G.toGraph.Adj u v → side u ≠ side v) →
          (∀ v ∈ iso, G.adj v = []) →
          2 / 3 ≤ A.prob G (fun muhat =>
            (TuranMatching.Clique.matchingNumber G.toGraph : ℝ) / α ≤ muhat ∧
              muhat ≤ (TuranMatching.Clique.matchingNumber G.toGraph : ℝ))) →
        ∀ q : ℝ, DistinctCostLE A q →
          cr * ((n : ℝ) ^ ((2 : ℝ) - 1 / ((r : ℝ) + 1)) /
            α ^ (3 * (r : ℝ) - 3 + 4 / ((r : ℝ) + 1))) ≤ q) ∧
    (∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ A : RandAlg n ℝ,
      (∀ G : AdjList n, 2 / 3 ≤ A.prob G (fun muhat =>
        muhat = (TuranMatching.Clique.matchingNumber G.toGraph : ℝ))) →
      ∀ q : ℝ, DistinctCostLE A q → c * (n : ℝ) ^ 2 ≤ q) ∧
    (∃ D : ℝ, ∀ n : ℕ, ∃ A : RandAlg n ℝ, A.CostLE (D * (n : ℝ) ^ 2) ∧
      ∀ G : AdjList n, 2 / 3 ≤ A.prob G (fun muhat =>
        muhat = (TuranMatching.Clique.matchingNumber G.toGraph : ℝ))) := by sorry

end NAMatchEst.Supplement
