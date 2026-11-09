-- Prove2me | Theorems.Thm_NAMatchEst_lemma_3_4
-- name    : NAMatchEst.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T02:56:00.973257+00:00
-- url     : https://prove2.me/theorems/7d814745-7c7c-469a-bc7a-f142c07323e6
-- title:
--   Lemma 3.4 — yes-case alternatives
-- statement:
--   Throughout, $n^{1/3}\le\alpha\le n^{1/2}$ is real and $k$ is an integer with $\alpha\le k\le n$ (the standing setup of §3.2, p.19); $C_0=2^{20}$, $c=10^5$ and $L=\ln(2n)$. We are in the main case $k>\alpha^2$ of §3.3.
--
--   Let $H\subseteq V_1$ and suppose $\mu(G)\ge k$. Then at least one of the following holds:
--
--   1. $|V_1|\ge k/8$;
--   2. $R_H\ge k\alpha/4$;
--   3. $G[W_3]$ contains a matching of size at least $k/2$.
--
--   Each alternative is detected by one of the three tests of the large-scale trial.
--
--   **Formalization Note** A matching of $G[W_3]$ is a matching subgraph of $G$ all of whose vertices lie in $W_3$.
--
--   Differences from the source:
--   - encoding: a simple undirected graph G on n vertices with fixed adjacency-list orderings → G : AdjList n on Fin n (ordered, duplicate-free, symmetric, loopless lists); reason: every simple graph with every ordering is an AdjList; same instances
--   - encoding: µ(G) → TuranMatching.Clique.matchingNumber G.toGraph; reason: the published matching number, the same quantity
--   - generalization: the standing assumption that n is sufficiently large (§3.2, p.19) → every n; reason: the statement is deterministic and holds for all n; it specializes to large n
-- source:
--   Khanna–Mukhopadhyay–Shah, Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), Lemma 3.4, p.22 (PDF 26)

import Mathlib
import Definitions.Def_TuranMatching_Clique_Setting
import Definitions.Def_NAMatchEst_AdjList
import Definitions.Def_NAMatchEst_AdjList_toGraph
import Definitions.Def_NAMatchEst_V1
import Definitions.Def_NAMatchEst_RH
import Definitions.Def_NAMatchEst_W3

namespace NAMatchEst

/-- **Lemma 3.4 (Yes-case alternatives).** Suppose that `µ(G) ⩾ k` and `H ⊆ V₁`. At least one of
the following holds: (i) `|V₁| ⩾ k/8`; (ii) `R_H ⩾ kα/4`; (iii) `G[W₃]` contains a matching of size
at least `k/2`.

Khanna–Mukhopadhyay–Shah, *Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation*, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), Lemma 3.4, p.22 (PDF 26), in the main case `k > α²` (§3.3, p.20) of the standing setup
(§3.2, p.19).

**Formalization Note** "`G[W₃]` contains a matching of size at least `k/2`" is a matching subgraph
of `G` with all its vertices in `W₃` and at least `k/2` edges. The source's standing "n
sufficiently large" is not assumed. -/
theorem lemma_3_4 (n : ℕ) (α : ℝ) (k : ℕ) :
    (n : ℝ) ^ ((1 : ℝ) / 3) ≤ α → α ≤ (n : ℝ) ^ ((1 : ℝ) / 2) → α ≤ k → (k : ℝ) ≤ n → α ^ 2 < k →
    ∀ (G : AdjList n) (H : Finset (Fin n)), k ≤ TuranMatching.Clique.matchingNumber G.toGraph → H ⊆ V1 G α k →
      (k : ℝ) / 8 ≤ (V1 G α k).card ∨ (k : ℝ) * α / 4 ≤ RH G α k H ∨
        ∃ M : G.toGraph.Subgraph, M.IsMatching ∧ M.verts ⊆ ↑(W3 G α k H) ∧
          (k : ℝ) / 2 ≤ M.edgeSet.ncard := by sorry

end NAMatchEst
