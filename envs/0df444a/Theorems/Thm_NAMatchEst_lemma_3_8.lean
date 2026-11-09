-- Prove2me | Theorems.Thm_NAMatchEst_lemma_3_8
-- name    : NAMatchEst.lemma_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T02:57:00.892322+00:00
-- url     : https://prove2.me/theorems/759d73e4-4561-4181-805d-b6707c8f6ed6
-- title:
--   Lemma 3.8 — completeness of the certified-edge test
-- statement:
--   Throughout, $n^{1/3}\le\alpha\le n^{1/2}$ is real and $k$ is an integer with $\alpha\le k\le n$ (the standing setup of §3.2, p.19); $C_0=2^{20}$, $c=10^5$ and $L=\ln(2n)$. We are in the main case $k>\alpha^2$ and $n$ is sufficiently large.
--
--   For every fixed set $H\subseteq V$ such that $G[W_3]$ contains a matching of size at least $k/2$, the certified-edge test accepts (that is, $Z_E\ge cL/4$) with probability at least $1-2n^{-30}$.
--
--   **Formalization Note** A matching of $G[W_3]$ is a matching subgraph of $G$ all of whose vertices lie in $W_3$.
--
--   Differences from the source:
--   - encoding: a simple undirected graph G on n vertices with fixed adjacency-list orderings → G : AdjList n on Fin n (ordered, duplicate-free, symmetric, loopless lists); reason: every simple graph with every ordering is an AdjList; same instances
--   - reading: the standing assumption of §3.2 that n exceeds a sufficiently large universal constant (p.19) → ∃ N₀, ∀ n ≥ N₀, with N₀ chosen before n, α, k; reason: the source's standing assumption, made explicit
--   - encoding: for every fixed set H → the test's output is its decision (record) as a function of H, evaluated at H; reason: the queries do not depend on H (p.22); same probabilities
--   - encoding: Bernoulli samples with probabilities p^L, p^R → product distribution bernDist with p clamped to [0,1]; reason: for n ≥ N₀ the source's assumption cL/√α ≤ 1 puts both probabilities in [0,1], where the clamp does nothing
-- source:
--   Khanna–Mukhopadhyay–Shah, Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), Lemma 3.8, p.25 (PDF 29)

import Mathlib
import Definitions.Def_NAMatchEst_AdjList
import Definitions.Def_NAMatchEst_AdjList_toGraph
import Definitions.Def_NAMatchEst_RandAlg
import Definitions.Def_NAMatchEst_RandAlg_prob
import Definitions.Def_NAMatchEst_cc
import Definitions.Def_NAMatchEst_L
import Definitions.Def_NAMatchEst_W3
import Definitions.Def_NAMatchEst_EdgeStats
import Definitions.Def_NAMatchEst_edgeTest

namespace NAMatchEst

/-- **Lemma 3.8 (Completeness of the certified-edge test).** For every fixed set `H` such that
`G[W₃]` contains a matching of size at least `k/2`, the certified-edge test accepts with probability
at least `1 − 2n^{−30}`.

Khanna–Mukhopadhyay–Shah, *Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation*, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), Lemma 3.8, p.25 (PDF 29), in the main case `k > α²` of the standing setup of §3.2, p.19
(PDF 23), including "n exceeds a sufficiently large universal constant".

**Formalization Note** The test accepts when `Z_E ⩾ kp^Lp^R/4 = cL/4` (19). "`G[W₃]` contains a
matching of size at least `k/2`" is a matching subgraph of `G` with all vertices in `W₃` and at
least `k/2` edges. -/
theorem lemma_3_8 : ∃ N₀ : ℕ, ∀ (n : ℕ) [NeZero n], N₀ ≤ n → ∀ (α : ℝ) (k : ℕ),
    (n : ℝ) ^ ((1 : ℝ) / 3) ≤ α → α ≤ (n : ℝ) ^ ((1 : ℝ) / 2) → α ≤ k → (k : ℝ) ≤ n → α ^ 2 < k →
    ∀ (G : AdjList n) (H : Finset (Fin n)),
      (∃ M : G.toGraph.Subgraph, M.IsMatching ∧ M.verts ⊆ ↑(W3 G α k H) ∧
        (k : ℝ) / 2 ≤ M.edgeSet.ncard) →
      1 - 2 * (n : ℝ) ^ (-30 : ℝ) ≤
        (edgeTest n α k).prob G (fun o => cc * L n / 4 ≤ ((o H).ZE : ℝ)) := by sorry

end NAMatchEst
