-- Prove2me | Theorems.Thm_NAMatchEst_Supplement_theorem_8
-- name    : NAMatchEst.Supplement.theorem_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:42:36.518052+00:00
-- url     : https://prove2.me/theorems/839ddcdb-ea7e-45a3-85cf-a1e2eec7c3c0
-- title:
--   Theorem 8 — non-adaptive gap tester $\mu(G)\ge k$ vs $\mu(G)\le k/(500\alpha\log n)$ with $\tilde O(n+nk^{2/3}/\alpha^2+nk/\alpha^4)$ queries
-- statement:
--   Logarithms are to base 2. Consider the two promised cases
--
--   $$
--   \text{Yes}:\ \mu(G)\ge k,\qquad \text{No}:\ \mu(G)\le\frac{k}{500\,\alpha\log n}.
--   $$
--
--   There are constants $D$ and $e\in\mathbb N$ such that for every $n\ge3$ and all reals $\alpha,k$ with
--
--   $$
--   50\log^2 n\le\alpha\le n^{1/3},\qquad \alpha\le k\le n,
--   $$
--
--   there is a randomized non-adaptive algorithm which makes at most
--
--   $$
--   D\cdot\Big(n+\frac{nk^{2/3}}{\alpha^2}+\frac{nk}{\alpha^4}\Big)\ln^e(2n)
--   $$
--
--   adjacency-list queries on every outcome of its randomness and which, on every graph $G$ on $n$ vertices and every list ordering, answers *yes* with probability at least $1-n^{-3}$ in the Yes case and *no* with probability at least $1-n^{-3}$ in the No case. On graphs satisfying neither promise either answer is allowed.
--
--   This peeling-based tester is the core of the proof of Theorem 7.
--
--   **Formalization Note** The hypotheses can only hold when $50\log^2 n\le n^{1/3}$, i.e. for very large $n$; this is the paper's range.
--
--   Differences from the source:
--   - encoding: a simple graph on n vertices with its adjacency lists in some order → G : AdjList n on Fin n (ordered, duplicate-free, symmetric, loopless lists); reason: every simple graph with every list ordering is an AdjList; same instances
--   - encoding: µ(G) → TuranMatching.Clique.matchingNumber G.toGraph; reason: the published matching number, the same quantity
--   - generalization: there is a randomized non-adaptive algorithm → there is a RandAlg (finite seed space with real weights, queries a function of the seed); reason: a RandAlg is a randomized non-adaptive algorithm, so the Lean statement implies the source's
--   - generalization: worst-case number of queries, identical queries answered once (p.20) → CostLE: the query list on every seed, every repetition charged; reason: a bound on the charged count on every seed implies the source's bound
--   - encoding: distinguishes the two promised cases → Bool output, true = the large-matching case; on graphs in neither case no requirement; reason: the paper's gap-tester convention (p.76)
--   - reading: Õ(n + nk^{2/3}/α² + nk/α⁴), log of base 2 (p.13) → D · (n + nk^{2/3}/α² + nk/α⁴) · L(n)^e with D, e chosen before n, α, k, L(n) = ln(2n); reason: the uniform reading of a universal constant and polylog factor; ln(2n) and log₂ n agree up to a constant factor for n ≥ 2
-- source:
--   Khanna–Mukhopadhyay–Shah, Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), the promised cases and Theorem 8, p.76 (PDF 80)

import Mathlib
import Definitions.Def_TuranMatching_Clique_Setting
import Definitions.Def_NAMatchEst_AdjList
import Definitions.Def_NAMatchEst_AdjList_toGraph
import Definitions.Def_NAMatchEst_RandAlg
import Definitions.Def_NAMatchEst_RandAlg_prob
import Definitions.Def_NAMatchEst_RandAlg_CostLE
import Definitions.Def_NAMatchEst_L

namespace NAMatchEst.Supplement

/-- **Theorem 8 (Non-adaptive adjacency-list gap tester).** Let `n ⩾ 3`. Suppose that
`50 log² n ⩽ α ⩽ n^{1/3}` and `α ⩽ k ⩽ n`. There is a randomized non-adaptive algorithm that
distinguishes the two promised cases `Yes : µ(G) ⩾ k` and `No : µ(G) ⩽ k/(500α log n)` with
probability at least `1 − n^{−3}` using `Õ(n + nk^{2/3}/α² + nk/α⁴)` adjacency-list queries. This is
a worst-case query bound. On graphs satisfying neither promise, either answer is allowed.

Khanna–Mukhopadhyay–Shah, *Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation*, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), the promised cases and Theorem 8, p.76 (PDF 80).

**Formalization Note**
1. Output `true` = Yes, `false` = No. `log` is base 2 (§2, p.13) in the hypotheses and the No
   promise.
2. `Õ(·)` is `D · (n + nk^{2/3}/α² + nk/α⁴) · L(n)^e` with `D`, `e` chosen before `n, α, k`;
   `L(n) = ln(2n)`. The bound holds on every seed, repetitions charged. `k` is real. -/
theorem theorem_8 : ∃ D : ℝ, ∃ e : ℕ, ∀ (n : ℕ) (α k : ℝ), 3 ≤ n →
    50 * Real.logb 2 n ^ 2 ≤ α → α ≤ (n : ℝ) ^ ((1 : ℝ) / 3) → α ≤ k → k ≤ n →
    ∃ A : RandAlg n Bool,
      A.CostLE (D * ((n : ℝ) + n * k ^ ((2 : ℝ) / 3) / α ^ 2 + n * k / α ^ 4) * L n ^ e) ∧
      ∀ G : AdjList n,
        (k ≤ (TuranMatching.Clique.matchingNumber G.toGraph : ℝ) →
          1 - (n : ℝ) ^ (-3 : ℝ) ≤ A.prob G (fun b => b = true)) ∧
        ((TuranMatching.Clique.matchingNumber G.toGraph : ℝ) ≤ k / (500 * α * Real.logb 2 n) →
          1 - (n : ℝ) ^ (-3 : ℝ) ≤ A.prob G (fun b => b = false)) := by sorry

end NAMatchEst.Supplement
