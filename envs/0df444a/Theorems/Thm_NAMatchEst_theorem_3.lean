-- Prove2me | Theorems.Thm_NAMatchEst_theorem_3
-- name    : NAMatchEst.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T02:55:56.145917+00:00
-- url     : https://prove2.me/theorems/ab5cbd49-47fc-4a6b-a823-b38e47d62733
-- title:
--   Theorem 3 — $O(\alpha)$-approximation of $\mu(G)$ with $\tilde O(n^{3/2}/\alpha^{3/2})$ non-adaptive queries
-- statement:
--   There are constants $C\ge1$ and $D$ such that the following holds. For every $n$ and every real $\alpha$ with $n^{1/3}\le\alpha\le n^{1/2}$ there is a randomized non-adaptive algorithm in the adjacency-list model which, given access to any simple undirected graph $G$ on $n$ vertices with $\mu(G)\ge1$ under any ordering of its adjacency lists, outputs a real estimate $\widehat\mu$ with
--
--   $$
--   \frac{\mu(G)}{C\alpha}\le\widehat\mu\le\mu(G)
--   $$
--
--   with probability at least $1-n^{-10}$, and which makes at most
--
--   $$
--   D\cdot\frac{n^{3/2}}{\alpha^{3/2}}\,\ln^3(2n)=\tilde O\Big(\frac{n^{3/2}}{\alpha^{3/2}}\Big)
--   $$
--
--   degree and indexed-neighbour queries on every outcome of its randomness. All queries are chosen before any oracle answer is received.
--
--   Here $\mu(G)$ is the maximum matching size. The theorem is the paper's non-adaptive upper bound for matching-size estimation, which the paper complements with matching lower bounds.
--
--   **Formalization Note** $C$ and $D$ are chosen before $n$ and $\alpha$, and the algorithm before the graph. Non-adaptivity is the type `RandAlg`: the queries are a function of the internal randomness.
--
--   Differences from the source:
--   - encoding: a simple undirected graph G on n vertices with fixed adjacency-list orderings → G : AdjList n on Fin n (ordered, duplicate-free, symmetric, loopless lists); reason: every simple graph with every ordering is an AdjList; same instances
--   - encoding: µ(G) → TuranMatching.Clique.matchingNumber G.toGraph; reason: the published matching number, the same quantity
--   - generalization: there is a randomized non-adaptive algorithm → there is a RandAlg: finite seed space with real weights, queries a function of the seed; reason: RandAlg is a subclass of the source's algorithms, so the Lean statement implies the source's
--   - generalization: identical oracle queries may be answered once (p.20) → every occurrence of a query is charged; reason: a bound on the charged count implies the source's bound
--   - reading: O(·) → one constant D chosen before n and α; reason: the uniform reading of a universal constant
--   - encoding: log³(2n), log of base 2 by the convention of §2 (p.13) → (ln 2n)³; reason: the bases differ by the constant factor (ln 2)³, absorbed in D
-- source:
--   Khanna–Mukhopadhyay–Shah, Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), Theorem 3, p.17 (PDF 21)

import Mathlib
import Definitions.Def_TuranMatching_Clique_Setting
import Definitions.Def_NAMatchEst_AdjList
import Definitions.Def_NAMatchEst_AdjList_toGraph
import Definitions.Def_NAMatchEst_RandAlg
import Definitions.Def_NAMatchEst_RandAlg_prob
import Definitions.Def_NAMatchEst_RandAlg_CostLE
import Definitions.Def_NAMatchEst_L

namespace NAMatchEst

/-- **Theorem 3.** There is a universal constant `C ⩾ 1` with the following property. For every
`n^{1/3} ⩽ α ⩽ n^{1/2}`, there is a randomized non-adaptive algorithm that, given adjacency-list
access to a simple undirected graph `G` on `n` vertices with `µ(G) ⩾ 1`, outputs an estimate `µ̂`
satisfying `µ(G)/(Cα) ⩽ µ̂ ⩽ µ(G)` with probability at least `1 − n^{−10}`. The algorithm makes at
most `O(n^{3/2}/α^{3/2} · log³(2n))` degree and indexed-neighbour queries in the worst case. All
queries are chosen before any oracle answers are received, and the guarantee holds for every
ordering of the adjacency lists.

Khanna–Mukhopadhyay–Shah, *Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation*, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), Theorem 3, p.17 (PDF 21).

**Formalization Note**
1. `C` and the constant `D` of the `O(·)` are chosen before `n` and `α`; the algorithm `A` is chosen
   before the graph, so one algorithm works for every simple graph on `Fin n` and every ordering of
   its lists (`AdjList n`).
2. Non-adaptivity is the type `RandAlg` (queries are a function of the seed); the query bound holds
   for every seed, with repetitions charged.
3. `log³(2n)` is written with the natural logarithm `L n = ln(2n)`; the base changes only `D`.
4. `µ(G)` is `TuranMatching.Clique.matchingNumber` of the graph; `µ̂` is real. -/
theorem theorem_3 : ∃ C : ℝ, 1 ≤ C ∧ ∃ D : ℝ, ∀ (n : ℕ) (α : ℝ),
    (n : ℝ) ^ ((1 : ℝ) / 3) ≤ α → α ≤ (n : ℝ) ^ ((1 : ℝ) / 2) →
    ∃ A : RandAlg n ℝ,
      A.CostLE (D * (n : ℝ) ^ ((3 : ℝ) / 2) / α ^ ((3 : ℝ) / 2) * L n ^ 3) ∧
      ∀ G : AdjList n, 1 ≤ TuranMatching.Clique.matchingNumber G.toGraph →
        1 - (n : ℝ) ^ (-10 : ℝ) ≤ A.prob G (fun muhat =>
          (TuranMatching.Clique.matchingNumber G.toGraph : ℝ) / (C * α) ≤ muhat ∧
            muhat ≤ (TuranMatching.Clique.matchingNumber G.toGraph : ℝ)) := by sorry

end NAMatchEst
