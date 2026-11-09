-- Prove2me | Theorems.Thm_NAMatchEst_lemma_3_5
-- name    : NAMatchEst.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T02:56:17.954987+00:00
-- url     : https://prove2.me/theorems/5bbf317a-c0f9-4287-baa4-99bc65436bce
-- title:
--   Lemma 3.5 — the first-layer degree test
-- statement:
--   Throughout, $n^{1/3}\le\alpha\le n^{1/2}$ is real and $k$ is an integer with $\alpha\le k\le n$ (the standing setup of §3.2, p.19); $C_0=2^{20}$, $c=10^5$ and $L=\ln(2n)$. Let $n$ be sufficiently large.
--
--   The first-layer degree test accepts with probability at least $1-n^{-30}$ if $|V_1|\ge k/8$, and rejects with probability at least $1-n^{-30}$ if $|V_1|\le k/100$. It uses $O(nL/k)$ queries, all of them degree queries.
--
--   **Formalization Note** One constant for the $O(\cdot)$ and one threshold for "sufficiently large", both chosen before $n$, $\alpha$, $k$; the cost bound holds for every seed.
--
--   Differences from the source:
--   - encoding: a simple undirected graph G on n vertices with fixed adjacency-list orderings → G : AdjList n on Fin n (ordered, duplicate-free, symmetric, loopless lists); reason: every simple graph with every ordering is an AdjList; same instances
--   - reading: the standing assumption of §3.2 that n exceeds a sufficiently large universal constant (p.19) → ∃ N₀, ∀ n ≥ N₀, with N₀ chosen before n, α, k; reason: the source's standing assumption, made explicit
--   - reading: O(·) → one constant D chosen before n, α and k; reason: the uniform reading of a universal constant
--   - generalization: Lemma 3.5 sits in §3.4 under “Continue to assume k > α²” → any integer k with α ≤ k ≤ n; reason: the source uses the same test in the small-scale regime (p.23, proof of Lemma 3.13); the statement specializes to k > α²
--   - generalization: identical oracle queries may be answered once (p.20) → every occurrence of a query is charged; reason: a bound on the charged count implies the source's bound
-- source:
--   Khanna–Mukhopadhyay–Shah, Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), Lemma 3.5, p.23 (PDF 27)

import Mathlib
import Definitions.Def_NAMatchEst_AdjList
import Definitions.Def_NAMatchEst_Query
import Definitions.Def_NAMatchEst_RandAlg
import Definitions.Def_NAMatchEst_RandAlg_prob
import Definitions.Def_NAMatchEst_RandAlg_CostLE
import Definitions.Def_NAMatchEst_L
import Definitions.Def_NAMatchEst_V1
import Definitions.Def_NAMatchEst_degTest

namespace NAMatchEst

/-- **Lemma 3.5.** The first-layer degree test accepts with probability at least `1 − n^{−30}` if
`|V₁| ⩾ k/8`, and rejects with probability at least `1 − n^{−30}` if `|V₁| ⩽ k/100`. It uses
`O(nL/k)` degree queries.

Khanna–Mukhopadhyay–Shah, *Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation*, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), Lemma 3.5, p.23 (PDF 27), under the standing setup of §3.2, p.19 (PDF 23):
`n^{1/3} ⩽ α ⩽ n^{1/2}`, `α ⩽ k ⩽ n`, and "n exceeds a sufficiently large universal constant".

**Formalization Note** One constant `D` for the `O(·)` and one threshold `N₀` for "sufficiently
large", both chosen before `n`, `α`, `k`. The cost bound is worst case (every seed), and every
query is a degree query. -/
theorem lemma_3_5 : ∃ D : ℝ, ∃ N₀ : ℕ, ∀ (n : ℕ) [NeZero n], N₀ ≤ n → ∀ (α : ℝ) (k : ℕ),
    (n : ℝ) ^ ((1 : ℝ) / 3) ≤ α → α ≤ (n : ℝ) ^ ((1 : ℝ) / 2) → α ≤ k → (k : ℝ) ≤ n →
    (∀ G : AdjList n, (k : ℝ) / 8 ≤ (V1 G α k).card →
      1 - (n : ℝ) ^ (-30 : ℝ) ≤ (degTest n α k).prob G (· = true)) ∧
    (∀ G : AdjList n, ((V1 G α k).card : ℝ) ≤ k / 100 →
      1 - (n : ℝ) ^ (-30 : ℝ) ≤ (degTest n α k).prob G (· = false)) ∧
    (degTest n α k).CostLE (D * n * L n / k) ∧
    ∀ ω, ∀ q ∈ (degTest n α k).queries ω, ∃ v, q = Query.deg v := by sorry

end NAMatchEst
