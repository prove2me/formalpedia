-- Prove2me | Theorems.Thm_NAMatchEst_lemma_3_13
-- name    : NAMatchEst.lemma_3_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T02:56:14.748902+00:00
-- url     : https://prove2.me/theorems/e4a415d4-8e39-4d2b-b176-7ce7958c44fb
-- title:
--   Lemma 3.13 — error of a small-scale trial
-- statement:
--   Throughout, $n^{1/3}\le\alpha\le n^{1/2}$ is real and $k$ is an integer with $\alpha\le k\le n$ (the standing setup of §3.2, p.19); $C_0=2^{20}$, $c=10^5$ and $L=\ln(2n)$. We are in the small-scale regime $\alpha\le k\le\alpha^2$ (§3.8) and $n$ is sufficiently large.
--
--   Before query-budget truncation, a small-scale trial errs with probability at most $1/10$ in either promised case: if $\mu(G)\ge k$ it outputs No with probability at most $1/10$, and if $\mu(G)<k/(C_0\alpha)$ it outputs Yes with probability at most $1/10$.
--
--   Differences from the source:
--   - encoding: a simple undirected graph G on n vertices with fixed adjacency-list orderings → G : AdjList n on Fin n (ordered, duplicate-free, symmetric, loopless lists); reason: every simple graph with every ordering is an AdjList; same instances
--   - encoding: µ(G) → TuranMatching.Clique.matchingNumber G.toGraph; reason: the published matching number, the same quantity
--   - reading: the standing assumption of §3.2 that n exceeds a sufficiently large universal constant (p.19) → ∃ N₀, ∀ n ≥ N₀, with N₀ chosen before n, α, k; reason: the source's standing assumption, made explicit
--   - encoding: Bernoulli samples with probabilities p^L, p^R → product distribution bernDist with p clamped to [0,1]; reason: for n ≥ N₀ the source's assumption cL/√α ≤ 1 puts both probabilities in [0,1], where the clamp does nothing
-- source:
--   Khanna–Mukhopadhyay–Shah, Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), Lemma 3.13, p.29 (PDF 33)

import Mathlib
import Definitions.Def_TuranMatching_Clique_Setting
import Definitions.Def_NAMatchEst_AdjList
import Definitions.Def_NAMatchEst_AdjList_toGraph
import Definitions.Def_NAMatchEst_RandAlg
import Definitions.Def_NAMatchEst_RandAlg_prob
import Definitions.Def_NAMatchEst_C0
import Definitions.Def_NAMatchEst_smallTrial

namespace NAMatchEst

/-- **Lemma 3.13.** Before query-budget truncation, a small-scale trial errs with probability at
most `1/10` in either promised case.

Khanna–Mukhopadhyay–Shah, *Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation*, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), Lemma 3.13, p.29 (PDF 33), for `α ⩽ k ⩽ α²` (§3.8, p.28) in the standing setup of §3.2,
p.19 (PDF 23), including "n exceeds a sufficiently large universal constant". The promised cases
are `µ(G) ⩾ k` and `µ(G) < k/(C₀α)` (Lemma 3.1, p.19).

**Formalization Note** "Errs" is: outputs No (`false`) in the yes-case, Yes (`true`) in the no-case.
One threshold `N₀`, chosen before `n`, `α`, `k`. -/
theorem lemma_3_13 : ∃ N₀ : ℕ, ∀ (n : ℕ) [NeZero n], N₀ ≤ n → ∀ (α : ℝ) (k : ℕ),
    (n : ℝ) ^ ((1 : ℝ) / 3) ≤ α → α ≤ (n : ℝ) ^ ((1 : ℝ) / 2) → α ≤ k → (k : ℝ) ≤ n → (k : ℝ) ≤ α ^ 2 →
    ∀ G : AdjList n,
      (k ≤ TuranMatching.Clique.matchingNumber G.toGraph → (smallTrial n α k).prob G (· = false) ≤ 1 / 10) ∧
      ((TuranMatching.Clique.matchingNumber G.toGraph : ℝ) < k / (C0 * α) →
        (smallTrial n α k).prob G (· = true) ≤ 1 / 10) := by sorry

end NAMatchEst
