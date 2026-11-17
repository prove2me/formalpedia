-- Prove2me | Theorems.Thm_NAMatchEst_Supplement_theorem_12
-- name    : NAMatchEst.Supplement.theorem_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:45:28.831188+00:00
-- url     : https://prove2.me/theorems/1c160e66-ed3d-4eb6-9a0b-5a15117e4b2d
-- title:
--   Theorem 12 — gap tester $\mu(G)<k/(10\alpha\log^2 n)$ vs $\mu(G)\ge k$ with $\tilde O(n/\alpha^{1/2})$ or $\tilde O(nk^{1/3}/\alpha)$ queries
-- statement:
--   Logarithms are to base 2. There is $e\in\mathbb N$ such that for every $c>0$ there is a constant $D$ with the following property. For every $n$, every real $\alpha$ with $n^{1/3}\le\alpha\le n^{2/3}$ and every real $k$ with $\alpha\log^3 n\le k\le n$ there is a randomized non-adaptive algorithm with output in $\{\text{yes},\text{no}\}$ which makes, on every outcome of its randomness, at most
--
--   $$
--   D\cdot\frac{n}{\alpha^{1/2}}\ln^e(2n)\ \text{ queries if } k\le\alpha^2,\qquad D\cdot\frac{nk^{1/3}}{\alpha}\ln^e(2n)\ \text{ queries if } k>\alpha^2,
--   $$
--
--   and which, on every graph $G$ on $n$ vertices (every list ordering), answers *no* with probability at least $1-n^{-c}$ if $\mu(G)<k/(10\alpha\log^2 n)$ and *yes* with probability at least $1-n^{-c}$ if $\mu(G)\ge k$. Either answer is allowed otherwise.
--
--   Run over all scales $k$ that are powers of two, this tester gives Theorem 11 (Lemma A.1).
--
--   Differences from the source:
--   - encoding: a simple graph on n vertices with its adjacency lists in some order → G : AdjList n on Fin n (ordered, duplicate-free, symmetric, loopless lists); reason: every simple graph with every list ordering is an AdjList; same instances
--   - encoding: µ(G) → TuranMatching.Clique.matchingNumber G.toGraph; reason: the published matching number, the same quantity
--   - generalization: there is a randomized non-adaptive algorithm → there is a RandAlg (finite seed space with real weights, queries a function of the seed); reason: a RandAlg is a randomized non-adaptive algorithm, so the Lean statement implies the source's
--   - generalization: worst-case number of queries, identical queries answered once (p.20) → CostLE: the query list on every seed, every repetition charged; reason: a bound on the charged count on every seed implies the source's bound
--   - encoding: distinguishes the two promised cases → Bool output, true = the large-matching case; on graphs in neither case no requirement; reason: the paper's gap-tester convention (p.76)
--   - reading: with probability 1 − 1/poly(n) → for every c > 0 a query constant D chosen after c, with success ≥ 1 − n^{−c}; reason: read as the paper's 'with high probability' (p.14), its stronger form
--   - reading: Õ(f), log of base 2 (p.13) → D · f · L(n)^e with D and e chosen before n, α (and k), L(n) = ln(2n); reason: the uniform reading of a universal constant and polylog factor; ln(2n) and log₂ n agree up to a constant factor for n ≥ 2
-- source:
--   Khanna–Mukhopadhyay–Shah, Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), Theorem 12, p.133 (PDF 137); with high probability, p.14 (PDF 18)

import Mathlib
import Definitions.Def_TuranMatching_Clique_Setting
import Definitions.Def_NAMatchEst_AdjList
import Definitions.Def_NAMatchEst_AdjList_toGraph
import Definitions.Def_NAMatchEst_RandAlg
import Definitions.Def_NAMatchEst_RandAlg_prob
import Definitions.Def_NAMatchEst_RandAlg_CostLE
import Definitions.Def_NAMatchEst_L

namespace NAMatchEst.Supplement

/-- **Theorem 12.** For every `n^{1/3} ⩽ α ⩽ n^{2/3}` and every parameter `k` satisfying
`α log³ n ⩽ k ⩽ n`, there exists a randomized non-adaptive algorithm that, given adjacency list
access to an input graph `G` on `n` vertices, with probability `1 − 1/poly(n)`, distinguishes
whether `µ(G) < k/(10α log² n)` or `µ(G) ⩾ k`. The algorithm makes `Õ(n/α^{1/2})` queries when
`k ⩽ α²`, and `Õ(nk^{1/3}/α)` queries when `k > α²`.

Khanna–Mukhopadhyay–Shah, *Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation*, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), Theorem 12, p.133 (PDF 137); "with high probability", p.14 (PDF 18).

**Formalization Note**
1. Output `true` = "`µ(G) ⩾ k`", `false` = "`µ(G) < k/(10α log² n)`"; either answer is allowed
   on a graph satisfying neither promise. General graphs on `Fin n`, every list ordering.
2. "`1 − 1/poly(n)`" is read as "with high probability" (p.14): for every `c > 0` a constant `D`,
   success `⩾ 1 − n^{−c}`. The polylog exponent `e` of `Õ` is chosen first.
3. The query bound is the case split `k ⩽ α²` / `k > α²`. `log` base 2 in the promise and the
   range of `k`; `L(n) = ln(2n)` in the `Õ`. -/
theorem theorem_12 : ∃ e : ℕ, ∀ c : ℝ, 0 < c → ∃ D : ℝ, ∀ (n : ℕ) (α k : ℝ),
    (n : ℝ) ^ ((1 : ℝ) / 3) ≤ α → α ≤ (n : ℝ) ^ ((2 : ℝ) / 3) →
    α * Real.logb 2 n ^ 3 ≤ k → k ≤ n →
    ∃ A : RandAlg n Bool,
      A.CostLE (D * (if k ≤ α ^ 2 then (n : ℝ) / α ^ ((1 : ℝ) / 2)
        else (n : ℝ) * k ^ ((1 : ℝ) / 3) / α) * L n ^ e) ∧
      ∀ G : AdjList n,
        ((TuranMatching.Clique.matchingNumber G.toGraph : ℝ) <
            k / (10 * α * Real.logb 2 n ^ 2) →
          1 - (n : ℝ) ^ (-c) ≤ A.prob G (fun b => b = false)) ∧
        (k ≤ (TuranMatching.Clique.matchingNumber G.toGraph : ℝ) →
          1 - (n : ℝ) ^ (-c) ≤ A.prob G (fun b => b = true)) := by sorry

end NAMatchEst.Supplement
