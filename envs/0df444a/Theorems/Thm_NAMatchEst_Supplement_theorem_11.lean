-- Prove2me | Theorems.Thm_NAMatchEst_Supplement_theorem_11
-- name    : NAMatchEst.Supplement.theorem_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:44:35.924196+00:00
-- url     : https://prove2.me/theorems/0c5e1460-0480-42b5-906a-c857a3ff9795
-- title:
--   Theorem 11 — $\alpha\log^3 n$-approximation with $\tilde O(n^{4/3}/\alpha)$ and $\tilde O(n/\alpha^{1/2})$ queries
-- statement:
--   Here $\mu(G)$ is the maximum matching size; logarithms are to base 2.
--
--   There is $e\in\mathbb N$ such that for every $c>0$ there is a constant $D$ with the following property, for every $n$ and every real $\alpha$.
--
--   1. If $n^{1/3}\le\alpha\le n^{1/2}$, there is a randomized non-adaptive algorithm making at most $D\,n^{4/3}\alpha^{-1}\ln^e(2n)$ queries on every outcome of its randomness, and
--   2. if $n^{1/2}\le\alpha\le n^{2/3}$, there is one making at most $D\,n\,\alpha^{-1/2}\ln^e(2n)$ queries,
--
--   which, on every graph $G$ on $n$ vertices with $\mu(G)\ge1$ (every list ordering), outputs $\widehat\mu$ with
--
--   $$
--   \frac{\mu(G)}{\alpha\log^3 n}\le\widehat\mu\le\mu(G)
--   $$
--
--   with probability at least $1-n^{-c}$.
--
--   This is the earlier upper bound of Appendix A; the second range extends the estimator beyond $\alpha=n^{1/2}$.
--
--   **Formalization Note** The approximation factor is exactly $\alpha\log^3 n$, with no constant. One algorithm per $(n,\alpha)$; at $\alpha=n^{1/2}$ both bounds are asserted.
--
--   Differences from the source:
--   - encoding: a simple graph on n vertices with its adjacency lists in some order → G : AdjList n on Fin n (ordered, duplicate-free, symmetric, loopless lists); reason: every simple graph with every list ordering is an AdjList; same instances
--   - encoding: µ(G) → TuranMatching.Clique.matchingNumber G.toGraph; reason: the published matching number, the same quantity
--   - generalization: there is a randomized non-adaptive algorithm → there is a RandAlg (finite seed space with real weights, queries a function of the seed); reason: a RandAlg is a randomized non-adaptive algorithm, so the Lean statement implies the source's
--   - generalization: worst-case number of queries, identical queries answered once (p.20) → CostLE: the query list on every seed, every repetition charged; reason: a bound on the charged count on every seed implies the source's bound
--   - reading: with high probability: ≥ 1 − n^{−c} for a large constant c that can be made arbitrarily large by increasing the number of queries by a constant factor (p.14) → for every c > 0 a query constant D chosen after c, the other constants chosen before c, with success ≥ 1 − n^{−c}; reason: the definition on p.14 read in its stronger form
--   - reading: Õ(f), log of base 2 (p.13) → D · f · L(n)^e with D and e chosen before n, α (and k), L(n) = ln(2n); reason: the uniform reading of a universal constant and polylog factor; ln(2n) and log₂ n agree up to a constant factor for n ≥ 2
-- source:
--   Khanna–Mukhopadhyay–Shah, Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), Theorem 11, p.133 (PDF 137); with high probability, p.14 (PDF 18)

import Mathlib
import Definitions.Def_TuranMatching_Clique_Setting
import Definitions.Def_NAMatchEst_AdjList
import Definitions.Def_NAMatchEst_AdjList_toGraph
import Definitions.Def_NAMatchEst_RandAlg
import Definitions.Def_NAMatchEst_RandAlg_prob
import Definitions.Def_NAMatchEst_RandAlg_CostLE
import Definitions.Def_NAMatchEst_L

namespace NAMatchEst.Supplement

/-- **Theorem 11.** There exists a randomized non-adaptive algorithm that, given adjacency list
access to an input graph `G` on `n` vertices with maximum matching size `µ(G) ⩾ 1`, with high
probability, outputs an `α log³ n` approximation to the size of the maximum matching using
`Õ(n^{4/3}/α)` queries for every `n^{1/3} ⩽ α ⩽ n^{1/2}` and using `Õ(n/α^{1/2})` queries for every
`n^{1/2} ⩽ α ⩽ n^{2/3}`.

Khanna–Mukhopadhyay–Shah, *Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation*, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), Theorem 11, p.133 (PDF 137); "with high probability", p.14 (PDF 18).

**Formalization Note**
1. The approximation factor is exactly `α log³ n` (`log` base 2, §2, p.13), no constant:
   `µ(G)/(α log³ n) ⩽ µ̂ ⩽ µ(G)`.
2. One algorithm per `(n, α)`, chosen before the graph; the two ranges are two conjuncts (they
   overlap at `α = n^{1/2}`, where both bounds are asserted).
3. "With high probability" and `Õ` as in Theorem 5 (`e` first, then `D` after `c`). -/
theorem theorem_11 : ∃ e : ℕ, ∀ c : ℝ, 0 < c → ∃ D : ℝ, ∀ (n : ℕ) (α : ℝ),
    ((n : ℝ) ^ ((1 : ℝ) / 3) ≤ α → α ≤ (n : ℝ) ^ ((1 : ℝ) / 2) →
      ∃ A : RandAlg n ℝ, A.CostLE (D * (n : ℝ) ^ ((4 : ℝ) / 3) / α * L n ^ e) ∧
        ∀ G : AdjList n, 1 ≤ TuranMatching.Clique.matchingNumber G.toGraph →
          1 - (n : ℝ) ^ (-c) ≤ A.prob G (fun muhat =>
            (TuranMatching.Clique.matchingNumber G.toGraph : ℝ) /
                (α * Real.logb 2 n ^ 3) ≤ muhat ∧
              muhat ≤ (TuranMatching.Clique.matchingNumber G.toGraph : ℝ))) ∧
    ((n : ℝ) ^ ((1 : ℝ) / 2) ≤ α → α ≤ (n : ℝ) ^ ((2 : ℝ) / 3) →
      ∃ A : RandAlg n ℝ, A.CostLE (D * (n : ℝ) / α ^ ((1 : ℝ) / 2) * L n ^ e) ∧
        ∀ G : AdjList n, 1 ≤ TuranMatching.Clique.matchingNumber G.toGraph →
          1 - (n : ℝ) ^ (-c) ≤ A.prob G (fun muhat =>
            (TuranMatching.Clique.matchingNumber G.toGraph : ℝ) /
                (α * Real.logb 2 n ^ 3) ≤ muhat ∧
              muhat ≤ (TuranMatching.Clique.matchingNumber G.toGraph : ℝ))) := by sorry

end NAMatchEst.Supplement
