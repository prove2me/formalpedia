-- Prove2me | Theorems.Thm_NAMatchEst_lemma_3_7
-- name    : NAMatchEst.lemma_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T02:56:22.720695+00:00
-- url     : https://prove2.me/theorems/9c26933f-9ccd-451a-b2d0-b22de4c449d7
-- title:
--   Lemma 3.7 — right-endpoint certification
-- statement:
--   Throughout, $n^{1/3}\le\alpha\le n^{1/2}$ is real and $k$ is an integer with $\alpha\le k\le n$ (the standing setup of §3.2, p.19); $C_0=2^{20}$, $c=10^5$ and $L=\ln(2n)$. We are in the main case $k>\alpha^2$ and $n$ is sufficiently large.
--
--   For every fixed set $H\subseteq V$ and every ordering of the adjacency lists, with probability at least $1-n^{-30}$,
--
--   $$
--   S^R\cap W_3\subseteq S^R_3\subseteq S^R\cap W_4,
--   $$
--
--   and deterministically (for every outcome of the randomness) $S^L\cap W_3\subseteq S^L_3\subseteq S^L\cap W_4$, where $S^L,S^R,S^L_3,S^R_3$ are the samples and retained sets of the certified-edge test.
--
--   Differences from the source:
--   - encoding: a simple undirected graph G on n vertices with fixed adjacency-list orderings → G : AdjList n on Fin n (ordered, duplicate-free, symmetric, loopless lists); reason: every simple graph with every ordering is an AdjList; same instances
--   - reading: the standing assumption of §3.2 that n exceeds a sufficiently large universal constant (p.19) → ∃ N₀, ∀ n ≥ N₀, with N₀ chosen before n, α, k; reason: the source's standing assumption, made explicit
--   - encoding: for every fixed set H → the test's output is its decision (record) as a function of H, evaluated at H; reason: the queries do not depend on H (p.22); same probabilities
--   - encoding: Bernoulli samples with probabilities p^L, p^R → product distribution bernDist with p clamped to [0,1]; reason: for n ≥ N₀ the source's assumption cL/√α ≤ 1 puts both probabilities in [0,1], where the clamp does nothing
-- source:
--   Khanna–Mukhopadhyay–Shah, Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), Lemma 3.7, p.25 (PDF 29)

import Mathlib
import Definitions.Def_NAMatchEst_AdjList
import Definitions.Def_NAMatchEst_RandAlg
import Definitions.Def_NAMatchEst_RandAlg_run
import Definitions.Def_NAMatchEst_RandAlg_prob
import Definitions.Def_NAMatchEst_W3
import Definitions.Def_NAMatchEst_W4
import Definitions.Def_NAMatchEst_EdgeStats
import Definitions.Def_NAMatchEst_edgeTest

namespace NAMatchEst

/-- **Lemma 3.7 (Right-endpoint certification).** For every fixed set `H`, with probability at least
`1 − n^{−30}`, `S^R ∩ W₃ ⊆ S^R_3 ⊆ S^R ∩ W₄`. Deterministically, `S^L ∩ W₃ ⊆ S^L_3 ⊆ S^L ∩ W₄`.

Khanna–Mukhopadhyay–Shah, *Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation*, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), Lemma 3.7, p.25 (PDF 29), in the main case `k > α²` of the standing setup of §3.2, p.19
(PDF 23), including "n exceeds a sufficiently large universal constant".

**Formalization Note** The statement holds for every `G : AdjList n`, i.e. for every ordering of
the adjacency lists ("This holds for every ordering of the adjacency list", p.25). "Deterministically"
is: for every seed. -/
theorem lemma_3_7 : ∃ N₀ : ℕ, ∀ (n : ℕ) [NeZero n], N₀ ≤ n → ∀ (α : ℝ) (k : ℕ),
    (n : ℝ) ^ ((1 : ℝ) / 3) ≤ α → α ≤ (n : ℝ) ^ ((1 : ℝ) / 2) → α ≤ k → (k : ℝ) ≤ n → α ^ 2 < k →
    ∀ (G : AdjList n) (H : Finset (Fin n)),
      1 - (n : ℝ) ^ (-30 : ℝ) ≤ (edgeTest n α k).prob G (fun o =>
        (o H).SR ∩ W3 G α k H ⊆ (o H).SR3 ∧ (o H).SR3 ⊆ (o H).SR ∩ W4 G α k H) ∧
      ∀ ω : (edgeTest n α k).Ω,
        ((edgeTest n α k).run G ω H).SL ∩ W3 G α k H ⊆ ((edgeTest n α k).run G ω H).SL3 ∧
        ((edgeTest n α k).run G ω H).SL3 ⊆ ((edgeTest n α k).run G ω H).SL ∩ W4 G α k H := by sorry

end NAMatchEst
