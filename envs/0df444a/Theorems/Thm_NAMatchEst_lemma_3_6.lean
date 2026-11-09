-- Prove2me | Theorems.Thm_NAMatchEst_lemma_3_6
-- name    : NAMatchEst.lemma_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T02:58:03.894527+00:00
-- url     : https://prove2.me/theorems/c84fd917-899a-4a90-aa4b-a1d232f1a6ce
-- title:
--   Lemma 3.6 — the residual-total test
-- statement:
--   Throughout, $n^{1/3}\le\alpha\le n^{1/2}$ is real and $k$ is an integer with $\alpha\le k\le n$ (the standing setup of §3.2, p.19); $C_0=2^{20}$, $c=10^5$ and $L=\ln(2n)$. We are in the main case $k>\alpha^2$ (§3.4) and $n$ is sufficiently large.
--
--   For every fixed set $H\subseteq V$, the residual-total test accepts with probability at least $1-n^{-30}$ if $R_H\ge k\alpha/4$, and rejects with probability at least $1-n^{-30}$ if $R_H\le k\alpha/100$. It uses $O(nkL/\alpha^3)$ queries.
--
--   **Formalization Note** One constant for the $O(\cdot)$ and one threshold for "sufficiently large", both chosen before $n$, $\alpha$, $k$; the cost bound holds for every seed.
--
--   Differences from the source:
--   - encoding: a simple undirected graph G on n vertices with fixed adjacency-list orderings → G : AdjList n on Fin n (ordered, duplicate-free, symmetric, loopless lists); reason: every simple graph with every ordering is an AdjList; same instances
--   - reading: the standing assumption of §3.2 that n exceeds a sufficiently large universal constant (p.19) → ∃ N₀, ∀ n ≥ N₀, with N₀ chosen before n, α, k; reason: the source's standing assumption, made explicit
--   - reading: O(·) → one constant D chosen before n, α and k; reason: the uniform reading of a universal constant
--   - encoding: for every fixed set H → the test's output is its decision (record) as a function of H, evaluated at H; reason: the queries do not depend on H (p.22); same probabilities
--   - generalization: identical oracle queries may be answered once (p.20) → every occurrence of a query is charged; reason: a bound on the charged count implies the source's bound
-- source:
--   Khanna–Mukhopadhyay–Shah, Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), Lemma 3.6, p.23 (PDF 27)

import Mathlib
import Definitions.Def_NAMatchEst_AdjList
import Definitions.Def_NAMatchEst_RandAlg
import Definitions.Def_NAMatchEst_RandAlg_prob
import Definitions.Def_NAMatchEst_RandAlg_CostLE
import Definitions.Def_NAMatchEst_L
import Definitions.Def_NAMatchEst_RH
import Definitions.Def_NAMatchEst_resTest

namespace NAMatchEst

/-- **Lemma 3.6.** For every fixed set `H`, the residual-total test accepts with probability at
least `1 − n^{−30}` if `R_H ⩾ kα/4`, and rejects with probability at least `1 − n^{−30}` if
`R_H ⩽ kα/100`. It uses `O(nkL/α³)` queries.

Khanna–Mukhopadhyay–Shah, *Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation*, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), Lemma 3.6, p.23 (PDF 27), in the main case `k > α²` (§3.4, p.22: "Continue to assume
k > α²") of the standing setup of §3.2, p.19 (PDF 23), including "n exceeds a sufficiently large
universal constant".

**Formalization Note** One constant `D` and one threshold `N₀`, chosen before `n`, `α`, `k`. The
test's output is its decision for every `H`; "for every fixed set `H`" is the probability of the
decision at that `H`. The cost bound is worst case. -/
theorem lemma_3_6 : ∃ D : ℝ, ∃ N₀ : ℕ, ∀ (n : ℕ) [NeZero n], N₀ ≤ n → ∀ (α : ℝ) (k : ℕ),
    (n : ℝ) ^ ((1 : ℝ) / 3) ≤ α → α ≤ (n : ℝ) ^ ((1 : ℝ) / 2) → α ≤ k → (k : ℝ) ≤ n → α ^ 2 < k →
    (∀ (G : AdjList n) (H : Finset (Fin n)), (k : ℝ) * α / 4 ≤ RH G α k H →
      1 - (n : ℝ) ^ (-30 : ℝ) ≤ (resTest n α k).prob G (fun f => f H = true)) ∧
    (∀ (G : AdjList n) (H : Finset (Fin n)), (RH G α k H : ℝ) ≤ k * α / 100 →
      1 - (n : ℝ) ^ (-30 : ℝ) ≤ (resTest n α k).prob G (fun f => f H = false)) ∧
    (resTest n α k).CostLE (D * n * k * L n / α ^ 3) := by sorry

end NAMatchEst
