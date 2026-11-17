-- Prove2me | Theorems.Thm_NAMatchEst_Supplement_theorem_5
-- name    : NAMatchEst.Supplement.theorem_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:40:21.944531+00:00
-- url     : https://prove2.me/theorems/5b4d0176-e364-4b22-8f3a-cfa7ecb740e0
-- title:
--   Theorem 5 — $O(\alpha\log^3 n)$-approximation of $\mu(G)$ with $\tilde O(n^2/\alpha^2)$ non-adaptive queries for $\alpha\ge n^{2/3}$
-- statement:
--   Here $\mu(G)$ is the maximum matching size; logarithms are to base 2.
--
--   There are constants $C>0$ and $e\in\mathbb N$ such that for every $c>0$ there is a constant $D$ with the following property. For every $n$ and every real $\alpha\ge n^{2/3}$ there is a randomized non-adaptive algorithm in the adjacency-list model which makes at most
--
--   $$
--   D\cdot\frac{n^2}{\alpha^2}\,\ln^e(2n)=\tilde O\Big(\frac{n^2}{\alpha^2}\Big)
--   $$
--
--   queries on every outcome of its randomness and which, on every graph $G$ on $n$ vertices with $\mu(G)\ge1$ and every ordering of its adjacency lists, outputs $\widehat\mu$ with
--
--   $$
--   \frac{\mu(G)}{C\,\alpha\log^3 n}\le\widehat\mu\le\mu(G)
--   $$
--
--   with probability at least $1-n^{-c}$.
--
--   This is the paper's upper bound in the large-$\alpha$ regime, obtained by reducing matching size to support-size testing of a random-neighbour distribution; Theorem 4 shows it is tight up to subpolynomial factors for $n^{2/3}\le\alpha\le n/K_0$.
--
--   **Formalization Note** The algorithm is chosen before the graph. Every query occurrence is charged.
--
--   Differences from the source:
--   - encoding: a simple graph on n vertices with its adjacency lists in some order → G : AdjList n on Fin n (ordered, duplicate-free, symmetric, loopless lists); reason: every simple graph with every list ordering is an AdjList; same instances
--   - encoding: µ(G) → TuranMatching.Clique.matchingNumber G.toGraph; reason: the published matching number, the same quantity
--   - generalization: there is a randomized non-adaptive algorithm → there is a RandAlg (finite seed space with real weights, queries a function of the seed); reason: a RandAlg is a randomized non-adaptive algorithm, so the Lean statement implies the source's
--   - generalization: worst-case number of queries, identical queries answered once (p.20) → CostLE: the query list on every seed, every repetition charged; reason: a bound on the charged count on every seed implies the source's bound
--   - reading: with high probability: ≥ 1 − n^{−c} for a large constant c that can be made arbitrarily large by increasing the number of queries by a constant factor (p.14) → for every c > 0 a query constant D chosen after c, the other constants chosen before c, with success ≥ 1 − n^{−c}; reason: the definition on p.14 read in its stronger form
--   - reading: Õ(f), log of base 2 (p.13) → D · f · L(n)^e with D and e chosen before n, α (and k), L(n) = ln(2n); reason: the uniform reading of a universal constant and polylog factor; ln(2n) and log₂ n agree up to a constant factor for n ≥ 2
--   - reading: an O(α log³ n) approximation → µ(G)/(Cα log₂³ n) ≤ µ̂ ≤ µ(G) with one constant C chosen first; reason: the uniform reading of O(·)
-- source:
--   Khanna–Mukhopadhyay–Shah, Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), Theorem 5, p.70 (PDF 74); with high probability, p.14 (PDF 18)

import Mathlib
import Definitions.Def_TuranMatching_Clique_Setting
import Definitions.Def_NAMatchEst_AdjList
import Definitions.Def_NAMatchEst_AdjList_toGraph
import Definitions.Def_NAMatchEst_RandAlg
import Definitions.Def_NAMatchEst_RandAlg_prob
import Definitions.Def_NAMatchEst_RandAlg_CostLE
import Definitions.Def_NAMatchEst_L

namespace NAMatchEst.Supplement

/-- **Theorem 5.** Let `α ⩾ n^{2/3}`. There is a randomized non-adaptive algorithm that, given
adjacency-list access to a graph `G = (V, E)` on `n` vertices with `µ(G) ⩾ 1`, outputs an
`O(α log³ n)` approximation to `µ(G)` with high probability using `Õ(n²/α²)` queries.

Khanna–Mukhopadhyay–Shah, *Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation*, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), Theorem 5, p.70 (PDF 74); "with high probability", p.14 (PDF 18).

**Formalization Note**
1. `O(α log³ n)`-approximation: one constant `C`, chosen first, with
   `µ(G)/(Cα log³ n) ⩽ µ̂ ⩽ µ(G)` (`log` base 2, §2, p.13).
2. "With high probability" (p.14): probability `⩾ 1 − n^{−c}`, where `c` can be made arbitrarily
   large by increasing the number of queries by a constant factor. So for every `c > 0` there is a
   query constant `D`, chosen after `c`; the approximation constant `C` and the polylog exponent `e`
   of `Õ` are chosen before `c`.
3. `Õ(n²/α²)` is `D · n²/α² · L(n)^e` with `L(n) = ln(2n)` (the base mission's `L`); the base of
   the logarithm only changes `D`. The bound holds on every seed, repetitions charged.
4. The algorithm is chosen before the graph and works for every adjacency-list ordering. -/
theorem theorem_5 : ∃ C : ℝ, 0 < C ∧ ∃ e : ℕ, ∀ c : ℝ, 0 < c → ∃ D : ℝ,
    ∀ (n : ℕ) (α : ℝ), (n : ℝ) ^ ((2 : ℝ) / 3) ≤ α →
      ∃ A : RandAlg n ℝ, A.CostLE (D * (n : ℝ) ^ 2 / α ^ 2 * L n ^ e) ∧
        ∀ G : AdjList n, 1 ≤ TuranMatching.Clique.matchingNumber G.toGraph →
          1 - (n : ℝ) ^ (-c) ≤ A.prob G (fun muhat =>
            (TuranMatching.Clique.matchingNumber G.toGraph : ℝ) /
                (C * α * Real.logb 2 n ^ 3) ≤ muhat ∧
              muhat ≤ (TuranMatching.Clique.matchingNumber G.toGraph : ℝ)) := by sorry

end NAMatchEst.Supplement
