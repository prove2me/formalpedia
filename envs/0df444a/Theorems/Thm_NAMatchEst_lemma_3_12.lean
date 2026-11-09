-- Prove2me | Theorems.Thm_NAMatchEst_lemma_3_12
-- name    : NAMatchEst.lemma_3_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T02:56:58.640423+00:00
-- url     : https://prove2.me/theorems/bf23f58e-f174-4f78-9a61-2b1481b32568
-- title:
--   Lemma 3.12 — error of a large-scale trial
-- statement:
--   Throughout, $n^{1/3}\le\alpha\le n^{1/2}$ is real and $k$ is an integer with $\alpha\le k\le n$ (the standing setup of §3.2, p.19); $C_0=2^{20}$, $c=10^5$ and $L=\ln(2n)$. We are in the main case $k>\alpha^2$ (§3.7) and $n$ is sufficiently large.
--
--   Before the query-budget truncation of §3.9, a large-scale trial errs with probability at most $1/10$ in either promised case: if $\mu(G)\ge k$ it outputs No with probability at most $1/10$, and if $\mu(G)<k/(C_0\alpha)$ it outputs Yes with probability at most $1/10$.
--
--   Differences from the source:
--   - encoding: a simple undirected graph G on n vertices with fixed adjacency-list orderings → G : AdjList n on Fin n (ordered, duplicate-free, symmetric, loopless lists); reason: every simple graph with every ordering is an AdjList; same instances
--   - encoding: µ(G) → TuranMatching.Clique.matchingNumber G.toGraph; reason: the published matching number, the same quantity
--   - reading: the standing assumption of §3.2 that n exceeds a sufficiently large universal constant (p.19) → ∃ N₀, ∀ n ≥ N₀, with N₀ chosen before n, α, k; reason: the source's standing assumption, made explicit
--   - encoding: Bernoulli samples with probabilities p^L, p^R → product distribution bernDist with p clamped to [0,1]; reason: for n ≥ N₀ the source's assumption cL/√α ≤ 1 puts both probabilities in [0,1], where the clamp does nothing
-- source:
--   Khanna–Mukhopadhyay–Shah, Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), Lemma 3.12, p.28 (PDF 32)

import Mathlib
import Definitions.Def_TuranMatching_Clique_Setting
import Definitions.Def_NAMatchEst_AdjList
import Definitions.Def_NAMatchEst_AdjList_toGraph
import Definitions.Def_NAMatchEst_RandAlg
import Definitions.Def_NAMatchEst_RandAlg_prob
import Definitions.Def_NAMatchEst_C0
import Definitions.Def_NAMatchEst_largeTrial

namespace NAMatchEst

/-- **Lemma 3.12.** Before the query-budget truncation in Section 3.9, a large-scale trial errs with
probability at most `1/10` in either promised case.

Khanna–Mukhopadhyay–Shah, *Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation*, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), Lemma 3.12, p.28 (PDF 32), for `k > α²` (§3.7) in the standing setup of §3.2, p.19
(PDF 23); the proof concludes "< 1/10 for all sufficiently large n" (p.28). The promised cases are
`µ(G) ⩾ k` (answer Yes) and `µ(G) < k/(C₀α)` (answer No) (Lemma 3.1, p.19).

**Formalization Note** "Errs" is: outputs No (`false`) in the yes-case, Yes (`true`) in the no-case.
One threshold `N₀` for "sufficiently large n", chosen before `n`, `α`, `k`. -/
theorem lemma_3_12 : ∃ N₀ : ℕ, ∀ (n : ℕ) [NeZero n], N₀ ≤ n → ∀ (α : ℝ) (k : ℕ),
    (n : ℝ) ^ ((1 : ℝ) / 3) ≤ α → α ≤ (n : ℝ) ^ ((1 : ℝ) / 2) → α ≤ k → (k : ℝ) ≤ n → α ^ 2 < k →
    ∀ G : AdjList n,
      (k ≤ TuranMatching.Clique.matchingNumber G.toGraph → (largeTrial n α k).prob G (· = false) ≤ 1 / 10) ∧
      ((TuranMatching.Clique.matchingNumber G.toGraph : ℝ) < k / (C0 * α) →
        (largeTrial n α k).prob G (· = true) ≤ 1 / 10) := by sorry

end NAMatchEst
