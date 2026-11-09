-- Prove2me | Theorems.Thm_NAMatchEst_lemma_3_9
-- name    : NAMatchEst.lemma_3_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T02:56:39.9885+00:00
-- url     : https://prove2.me/theorems/6ea5a18e-c905-4a08-bd22-217354acdec7
-- title:
--   Lemma 3.9 — soundness of the certified-edge test
-- statement:
--   Throughout, $n^{1/3}\le\alpha\le n^{1/2}$ is real and $k$ is an integer with $\alpha\le k\le n$ (the standing setup of §3.2, p.19); $C_0=2^{20}$, $c=10^5$ and $L=\ln(2n)$. We are in the main case $k>\alpha^2$ and $n$ is sufficiently large.
--
--   For every fixed set $H\subseteq V_1$ in a no-instance, $\mu(G)<k/(C_0\alpha)$, the certified-edge test accepts (that is, $Z_E\ge cL/4$) with probability at most
--
--   $$
--   \frac{64}{C_0}+n^{-30}.
--   $$
--
--   Differences from the source:
--   - encoding: a simple undirected graph G on n vertices with fixed adjacency-list orderings → G : AdjList n on Fin n (ordered, duplicate-free, symmetric, loopless lists); reason: every simple graph with every ordering is an AdjList; same instances
--   - encoding: µ(G) → TuranMatching.Clique.matchingNumber G.toGraph; reason: the published matching number, the same quantity
--   - reading: the standing assumption of §3.2 that n exceeds a sufficiently large universal constant (p.19) → ∃ N₀, ∀ n ≥ N₀, with N₀ chosen before n, α, k; reason: the source's standing assumption, made explicit
--   - encoding: for every fixed set H → the test's output is its decision (record) as a function of H, evaluated at H; reason: the queries do not depend on H (p.22); same probabilities
--   - encoding: Bernoulli samples with probabilities p^L, p^R → product distribution bernDist with p clamped to [0,1]; reason: for n ≥ N₀ the source's assumption cL/√α ≤ 1 puts both probabilities in [0,1], where the clamp does nothing
-- source:
--   Khanna–Mukhopadhyay–Shah, Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), Lemma 3.9, p.26 (PDF 30)

import Mathlib
import Definitions.Def_TuranMatching_Clique_Setting
import Definitions.Def_NAMatchEst_AdjList
import Definitions.Def_NAMatchEst_AdjList_toGraph
import Definitions.Def_NAMatchEst_RandAlg
import Definitions.Def_NAMatchEst_RandAlg_prob
import Definitions.Def_NAMatchEst_C0
import Definitions.Def_NAMatchEst_cc
import Definitions.Def_NAMatchEst_L
import Definitions.Def_NAMatchEst_V1
import Definitions.Def_NAMatchEst_EdgeStats
import Definitions.Def_NAMatchEst_edgeTest

namespace NAMatchEst

/-- **Lemma 3.9 (Soundness of the certified-edge test).** For every fixed set `H ⊆ V₁` in a
no-instance (`µ(G) < k/(C₀α)`), the certified-edge test accepts with probability at most
`64/C₀ + n^{−30}`.

Khanna–Mukhopadhyay–Shah, *Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation*, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), Lemma 3.9, p.26 (PDF 30), in the main case `k > α²` of the standing setup of §3.2, p.19
(PDF 23), including "n exceeds a sufficiently large universal constant"; a no-instance is
`µ(G) < k/(C₀α)` (Lemma 3.1, p.19).

**Formalization Note** The test accepts when `Z_E ⩾ cL/4` (19). -/
theorem lemma_3_9 : ∃ N₀ : ℕ, ∀ (n : ℕ) [NeZero n], N₀ ≤ n → ∀ (α : ℝ) (k : ℕ),
    (n : ℝ) ^ ((1 : ℝ) / 3) ≤ α → α ≤ (n : ℝ) ^ ((1 : ℝ) / 2) → α ≤ k → (k : ℝ) ≤ n → α ^ 2 < k →
    ∀ (G : AdjList n) (H : Finset (Fin n)), H ⊆ V1 G α k →
      (TuranMatching.Clique.matchingNumber G.toGraph : ℝ) < k / (C0 * α) →
      (edgeTest n α k).prob G (fun o => cc * L n / 4 ≤ ((o H).ZE : ℝ)) ≤
        64 / C0 + (n : ℝ) ^ (-30 : ℝ) := by sorry

end NAMatchEst
