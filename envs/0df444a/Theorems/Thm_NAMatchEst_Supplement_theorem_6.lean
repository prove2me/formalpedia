-- Prove2me | Theorems.Thm_NAMatchEst_Supplement_theorem_6
-- name    : NAMatchEst.Supplement.theorem_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:41:29.844655+00:00
-- url     : https://prove2.me/theorems/77e5b691-3fd3-4c2b-83fd-e3737cd43bad
-- title:
--   Theorem 6 — gap tester $\mu(G)<k/(10\alpha\log^2 n)$ vs $\mu(G)\ge k$ on bipartite graphs with $\tilde O(nk/\alpha^2)$ queries
-- statement:
--   Let $G=(L\cup R,E)$ be a bipartite graph with $|L|=|R|=n$, the sides known to the algorithm; logarithms are to base 2.
--
--   There is $e\in\mathbb N$ such that for every $c>0$ there is a constant $D$ with the following property. For every $n$, every real $\alpha\ge n^{2/3}$ and every real $k$ with $\alpha\log^3 n\le k\le n$ there is a randomized non-adaptive algorithm with output in $\{\text{yes},\text{no}\}$ which makes at most
--
--   $$
--   D\cdot\frac{nk}{\alpha^2}\,\ln^e(2n)=\tilde O\Big(\frac{nk}{\alpha^2}\Big)
--   $$
--
--   queries on every outcome of its randomness and which, on every such bipartite $G$ (every list ordering),
--
--   1. answers *no* with probability at least $1-n^{-c}$ if $\mu(G)<\dfrac{k}{10\,\alpha\log^2 n}$, and
--   2. answers *yes* with probability at least $1-n^{-c}$ if $\mu(G)\ge k$.
--
--   On graphs satisfying neither condition either answer is allowed. Combined over the scales $k$, this gap tester gives the estimator of Theorem 5.
--
--   **Formalization Note** The graph has vertex set $\{0,\dots,2n-1\}$ with $L=\{v<n\}$; every edge joins $L$ and $R$.
--
--   Differences from the source:
--   - encoding: a bipartite graph G = (L ∪ R, E) with |L| = |R| = n → G : AdjList (2n) with L = {v < n}, R the rest, every edge between L and R; reason: the paper's bipartite convention |V| = 2n (p.13); same instances
--   - encoding: µ(G) → TuranMatching.Clique.matchingNumber G.toGraph; reason: the published matching number, the same quantity
--   - generalization: there is a randomized non-adaptive algorithm → there is a RandAlg (finite seed space with real weights, queries a function of the seed); reason: a RandAlg is a randomized non-adaptive algorithm, so the Lean statement implies the source's
--   - generalization: worst-case number of queries, identical queries answered once (p.20) → CostLE: the query list on every seed, every repetition charged; reason: a bound on the charged count on every seed implies the source's bound
--   - encoding: distinguishes the two promised cases → Bool output, true = the large-matching case; on graphs in neither case no requirement; reason: the paper's gap-tester convention (p.76)
--   - reading: with high probability: ≥ 1 − n^{−c} for a large constant c that can be made arbitrarily large by increasing the number of queries by a constant factor (p.14) → for every c > 0 a query constant D chosen after c, the other constants chosen before c, with success ≥ 1 − n^{−c}; reason: the definition on p.14 read in its stronger form
--   - reading: Õ(f), log of base 2 (p.13) → D · f · L(n)^e with D and e chosen before n, α (and k), L(n) = ln(2n); reason: the uniform reading of a universal constant and polylog factor; ln(2n) and log₂ n agree up to a constant factor for n ≥ 2
-- source:
--   Khanna–Mukhopadhyay–Shah, Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), Theorem 6, p.70 (PDF 74); with high probability, p.14 (PDF 18); bipartite convention, p.13 (PDF 17)

import Mathlib
import Definitions.Def_TuranMatching_Clique_Setting
import Definitions.Def_NAMatchEst_AdjList
import Definitions.Def_NAMatchEst_AdjList_toGraph
import Definitions.Def_NAMatchEst_RandAlg
import Definitions.Def_NAMatchEst_RandAlg_prob
import Definitions.Def_NAMatchEst_RandAlg_CostLE
import Definitions.Def_NAMatchEst_L

namespace NAMatchEst.Supplement

/-- **Theorem 6.** Assume `α ⩾ n^{2/3}`. For every `k` with `α log³ n ⩽ k ⩽ n`, there is a randomized
non-adaptive algorithm that, given adjacency-list access to a bipartite graph `G = (L ∪ R, E)` with
`|L| = |R| = n`, distinguishes `µ(G) < k/(10α log² n)` from `µ(G) ⩾ k` with high probability using
`Õ(nk/α²)` queries.

Khanna–Mukhopadhyay–Shah, *Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation*, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), Theorem 6, p.70 (PDF 74); "with high probability", p.14 (PDF 18); bipartite convention, p.13
(PDF 17).

**Formalization Note**
1. The graph has `2n` vertices `Fin (2 * n)`; `L = {v | v < n}`, `R` the rest, known to the
   algorithm; every edge joins `L` and `R`.
2. Output `true` = "`µ(G) ⩾ k`", `false` = "`µ(G) < k/(10α log² n)`". On a graph satisfying
   neither promise either answer is allowed.
3. "With high probability" and `Õ` as in Theorem 5: the polylog exponent `e` first, then for every
   `c > 0` a constant `D`; success `⩾ 1 − n^{−c}` in each promised case. `log` is base 2 in the
   promise; `L(n) = ln(2n)` in the `Õ`. `k` is real. -/
theorem theorem_6 : ∃ e : ℕ, ∀ c : ℝ, 0 < c → ∃ D : ℝ,
    ∀ (n : ℕ) (α k : ℝ), (n : ℝ) ^ ((2 : ℝ) / 3) ≤ α →
      α * Real.logb 2 n ^ 3 ≤ k → k ≤ n →
      ∃ A : RandAlg (2 * n) Bool, A.CostLE (D * n * k / α ^ 2 * L n ^ e) ∧
        ∀ G : AdjList (2 * n), (∀ u v, G.toGraph.Adj u v → ((u : ℕ) < n ↔ n ≤ (v : ℕ))) →
          ((TuranMatching.Clique.matchingNumber G.toGraph : ℝ) <
              k / (10 * α * Real.logb 2 n ^ 2) →
            1 - (n : ℝ) ^ (-c) ≤ A.prob G (fun b => b = false)) ∧
          (k ≤ (TuranMatching.Clique.matchingNumber G.toGraph : ℝ) →
            1 - (n : ℝ) ^ (-c) ≤ A.prob G (fun b => b = true)) := by sorry

end NAMatchEst.Supplement
