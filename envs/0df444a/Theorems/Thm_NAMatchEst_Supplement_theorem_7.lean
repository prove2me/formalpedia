-- Prove2me | Theorems.Thm_NAMatchEst_Supplement_theorem_7
-- name    : NAMatchEst.Supplement.theorem_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:42:02.872776+00:00
-- url     : https://prove2.me/theorems/0758a0dc-9145-49db-911d-e476c82832df
-- title:
--   Theorem 7 — $\alpha$-approximation of $\mu(G)$ with $\tilde O(\min\{n^2, n^{5/3}/\alpha^2+n^2/\alpha^4\})$ non-adaptive queries
-- statement:
--   Here $\mu(G)$ is the maximum matching size and an estimate $\widehat\mu$ is an **$\alpha$-approximation** if $\mu(G)/\alpha\le\widehat\mu\le\mu(G)$.
--
--   There is $e\in\mathbb N$ such that for every $c>0$ there is a constant $D$ with the following property. For every $n$ and every real $\alpha$ with $1\le\alpha\le n^{1/3}$ there is a randomized non-adaptive adjacency-list algorithm which makes at most
--
--   $$
--   D\cdot\min\Big\{n^2,\ \frac{n^{5/3}}{\alpha^2}+\frac{n^2}{\alpha^4}\Big\}\ln^e(2n)
--   $$
--
--   queries on every outcome of its randomness and which, on every simple graph $G$ on $n$ vertices (the empty graph included) and every ordering of its adjacency lists, returns an $\alpha$-approximation of $\mu(G)$ with probability at least $1-n^{-c}$.
--
--   This is the paper's superlinear tradeoff for small approximation factors; it is complemented by the lower bounds of Theorem 9.
--
--   **Formalization Note** The algorithm is chosen before the graph. No promise $\mu(G)\ge1$: on the empty graph the output must be $0$.
--
--   Differences from the source:
--   - encoding: a simple graph on n vertices with its adjacency lists in some order → G : AdjList n on Fin n (ordered, duplicate-free, symmetric, loopless lists); reason: every simple graph with every list ordering is an AdjList; same instances
--   - encoding: µ(G) → TuranMatching.Clique.matchingNumber G.toGraph; reason: the published matching number, the same quantity
--   - generalization: there is a randomized non-adaptive algorithm → there is a RandAlg (finite seed space with real weights, queries a function of the seed); reason: a RandAlg is a randomized non-adaptive algorithm, so the Lean statement implies the source's
--   - generalization: worst-case number of queries, identical queries answered once (p.20) → CostLE: the query list on every seed, every repetition charged; reason: a bound on the charged count on every seed implies the source's bound
--   - reading: with high probability: ≥ 1 − n^{−c} for a large constant c that can be made arbitrarily large by increasing the number of queries by a constant factor (p.14) → for every c > 0 a query constant D chosen after c, the other constants chosen before c, with success ≥ 1 − n^{−c}; reason: the definition on p.14 read in its stronger form
--   - reading: Õ(f), log of base 2 (p.13) → D · f · L(n)^e with D and e chosen before n, α (and k), L(n) = ln(2n); reason: the uniform reading of a universal constant and polylog factor; ln(2n) and log₂ n agree up to a constant factor for n ≥ 2
--   - reading: for every simple n-vertex graph G and every 1 ≤ α ≤ n^{1/3}, there is an algorithm → for every n and α there is one algorithm A that works for every G; reason: read literally (graph before algorithm) the statement is trivial; the proof (p.91) builds one algorithm for all graphs, the stronger reading
-- source:
--   Khanna–Mukhopadhyay–Shah, Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), Theorem 7, p.75 (PDF 79); with high probability, p.14 (PDF 18)

import Mathlib
import Definitions.Def_TuranMatching_Clique_Setting
import Definitions.Def_NAMatchEst_AdjList
import Definitions.Def_NAMatchEst_AdjList_toGraph
import Definitions.Def_NAMatchEst_RandAlg
import Definitions.Def_NAMatchEst_RandAlg_prob
import Definitions.Def_NAMatchEst_RandAlg_CostLE
import Definitions.Def_NAMatchEst_L

namespace NAMatchEst.Supplement

/-- **Theorem 7 (Superlinear query-approximation tradeoff).** For every simple `n`-vertex graph `G`
and every `1 ⩽ α ⩽ n^{1/3}`, there is a randomized non-adaptive adjacency-list algorithm using
`Õ(min{n², n^{5/3}/α² + n²/α⁴})` queries that, with high probability, returns an `α`-approximation
to `µ(G)`. The query bound is a worst-case bound, and no promise that `G` is nonempty is required.

Khanna–Mukhopadhyay–Shah, *Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation*, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), Theorem 7, p.75 (PDF 79); "with high probability", p.14 (PDF 18).

**Formalization Note**
1. The algorithm is chosen before the graph (one algorithm for all `G` on `Fin n` and every
   ordering of the lists); the printed order "for every `G` … there is an algorithm" read literally
   would be trivial, and the proof (p.91) gives one algorithm.
2. Exact `α`-approximation `µ(G)/α ⩽ µ̂ ⩽ µ(G)` (§2, p.13), on every graph, the empty graph
   included (no `µ(G) ⩾ 1` hypothesis).
3. "With high probability" and `Õ` as in Theorem 5. -/
theorem theorem_7 : ∃ e : ℕ, ∀ c : ℝ, 0 < c → ∃ D : ℝ,
    ∀ (n : ℕ) (α : ℝ), 1 ≤ α → α ≤ (n : ℝ) ^ ((1 : ℝ) / 3) →
      ∃ A : RandAlg n ℝ,
        A.CostLE (D * min ((n : ℝ) ^ 2)
          ((n : ℝ) ^ ((5 : ℝ) / 3) / α ^ 2 + (n : ℝ) ^ 2 / α ^ 4) * L n ^ e) ∧
        ∀ G : AdjList n,
          1 - (n : ℝ) ^ (-c) ≤ A.prob G (fun muhat =>
            (TuranMatching.Clique.matchingNumber G.toGraph : ℝ) / α ≤ muhat ∧
              muhat ≤ (TuranMatching.Clique.matchingNumber G.toGraph : ℝ)) := by sorry

end NAMatchEst.Supplement
