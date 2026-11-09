-- Prove2me | Theorems.Thm_NAMatchEst_lemma_3_1
-- name    : NAMatchEst.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T02:55:23.921371+00:00
-- url     : https://prove2.me/theorems/dee59752-b6cf-4c1a-95ef-4bfaaee46774
-- title:
--   Lemma 3.1 — parameterized gap tester
-- statement:
--   There is a constant $D$ such that the following holds. For every $n$, every real $\alpha$ with $n^{1/3}\le\alpha\le n^{1/2}$ and every integer $k$ with $\alpha\le k\le n$, there is a randomized non-adaptive algorithm in the adjacency-list model which, for every simple graph $G$ on $n$ vertices and every ordering of its adjacency lists,
--
--   1. outputs Yes with probability at least $1-n^{-20}$ when $\mu(G)\ge k$;
--   2. outputs No with probability at least $1-n^{-20}$ when $\mu(G)<k/(C_0\alpha)$, where $C_0=2^{20}$;
--
--   and which makes, on every outcome of its randomness, at most
--
--   $$
--   D\,L^2\cdot\begin{cases} n/\sqrt\alpha, & k\le\alpha^2,\\ n\sqrt k/\alpha^{3/2}, & k>\alpha^2\end{cases}\qquad (2)
--   $$
--
--   queries, where $L=\ln(2n)$. Between the two promises nothing is required, and the promise $\mu(G)\ge1$ is not assumed.
--
--   The gap tester is run at geometrically increasing scales $k$ to estimate $\mu(G)$ in Theorem 3.
--
--   Differences from the source:
--   - encoding: a simple undirected graph G on n vertices with fixed adjacency-list orderings → G : AdjList n on Fin n (ordered, duplicate-free, symmetric, loopless lists); reason: every simple graph with every ordering is an AdjList; same instances
--   - encoding: µ(G) → TuranMatching.Clique.matchingNumber G.toGraph; reason: the published matching number, the same quantity
--   - generalization: there is a randomized non-adaptive algorithm → there is a RandAlg: finite seed space with real weights, queries a function of the seed; reason: RandAlg is a subclass of the source's algorithms, so the Lean statement implies the source's
--   - generalization: identical oracle queries may be answered once (p.20) → every occurrence of a query is charged; reason: a bound on the charged count implies the source's bound
--   - reading: O(·) → one constant D chosen before n, α and k; reason: the uniform reading of a universal constant
-- source:
--   Khanna–Mukhopadhyay–Shah, Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), Lemma 3.1, p.19 (PDF 23)

import Mathlib
import Definitions.Def_TuranMatching_Clique_Setting
import Definitions.Def_NAMatchEst_AdjList
import Definitions.Def_NAMatchEst_AdjList_toGraph
import Definitions.Def_NAMatchEst_RandAlg
import Definitions.Def_NAMatchEst_RandAlg_prob
import Definitions.Def_NAMatchEst_RandAlg_CostLE
import Definitions.Def_NAMatchEst_C0
import Definitions.Def_NAMatchEst_L

namespace NAMatchEst

/-- **Lemma 3.1 (Parameterized gap tester).** For every `n^{1/3} ⩽ α ⩽ n^{1/2}` and every integer
`k` with `α ⩽ k ⩽ n`, there is a randomized non-adaptive algorithm that outputs Yes when
`µ(G) ⩾ k` and No when `µ(G) < k/(C₀α)`, with probability at least `1 − n^{−20}` in either
promised case. Its worst-case number of queries is
`O(L² · (n/√α if k ⩽ α², n√k/α^{3/2} if k > α²))` (2). The lemma does not require `µ(G) ⩾ 1`.

Khanna–Mukhopadhyay–Shah, *Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation*, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), Lemma 3.1, p.19 (PDF 23), with `C₀ = 2²⁰`, `L = ln(2n)` (§3.2, p.19).

**Formalization Note** One constant `D` for the `O(·)`, chosen before `n`, `α`, `k`. The algorithm
is a `RandAlg` (non-adaptive by construction) with Yes = `true`; it is chosen before the graph, so
the guarantee holds for every simple graph on `n` vertices and every ordering of its adjacency
lists. The query bound holds for every seed. -/
theorem lemma_3_1 : ∃ D : ℝ, ∀ (n : ℕ) (α : ℝ) (k : ℕ),
    (n : ℝ) ^ ((1 : ℝ) / 3) ≤ α → α ≤ (n : ℝ) ^ ((1 : ℝ) / 2) → α ≤ k → (k : ℝ) ≤ n →
    ∃ A : RandAlg n Bool,
      A.CostLE (D * L n ^ 2 *
        (if (k : ℝ) ≤ α ^ 2 then n / Real.sqrt α else n * Real.sqrt k / α ^ ((3 : ℝ) / 2))) ∧
      ∀ G : AdjList n,
        (k ≤ TuranMatching.Clique.matchingNumber G.toGraph → 1 - (n : ℝ) ^ (-20 : ℝ) ≤ A.prob G (· = true)) ∧
        ((TuranMatching.Clique.matchingNumber G.toGraph : ℝ) < k / (C0 * α) →
          1 - (n : ℝ) ^ (-20 : ℝ) ≤ A.prob G (· = false)) := by sorry

end NAMatchEst
