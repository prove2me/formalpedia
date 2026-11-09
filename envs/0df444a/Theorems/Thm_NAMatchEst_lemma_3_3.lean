-- Prove2me | Theorems.Thm_NAMatchEst_lemma_3_3
-- name    : NAMatchEst.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T02:58:33.395328+00:00
-- url     : https://prove2.me/theorems/5e2ab2c5-1f5a-4908-af77-dd7975d3372c
-- title:
--   Lemma 3.3 — no-case structure
-- statement:
--   Throughout, $n^{1/3}\le\alpha\le n^{1/2}$ is real and $k$ is an integer with $\alpha\le k\le n$ (the standing setup of §3.2, p.19); $C_0=2^{20}$, $c=10^5$ and $L=\ln(2n)$. We are in the main case $k>\alpha^2$ of §3.3.
--
--   Let $H\subseteq V$ with $V_1^H\subseteq H\subseteq V_1$, and suppose $\mu(G)<k/(C_0\alpha)$. Then
--
--   $$
--   |V_1|\le\frac{k}{100}\qquad\text{and}\qquad R_H<\frac{k\alpha}{100}.
--   $$
--
--   In a no-instance the first two quantities tested by the large-scale trial are therefore below their thresholds.
--
--   Differences from the source:
--   - encoding: a simple undirected graph G on n vertices with fixed adjacency-list orderings → G : AdjList n on Fin n (ordered, duplicate-free, symmetric, loopless lists); reason: every simple graph with every ordering is an AdjList; same instances
--   - encoding: µ(G) → TuranMatching.Clique.matchingNumber G.toGraph; reason: the published matching number, the same quantity
--   - generalization: the standing assumption that n is sufficiently large (§3.2, p.19) → every n; reason: the statement is deterministic and holds for all n; it specializes to large n
-- source:
--   Khanna–Mukhopadhyay–Shah, Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), Lemma 3.3, p.21 (PDF 25)

import Mathlib
import Definitions.Def_TuranMatching_Clique_Setting
import Definitions.Def_NAMatchEst_AdjList
import Definitions.Def_NAMatchEst_AdjList_toGraph
import Definitions.Def_NAMatchEst_C0
import Definitions.Def_NAMatchEst_V1
import Definitions.Def_NAMatchEst_V1H
import Definitions.Def_NAMatchEst_RH

namespace NAMatchEst

/-- **Lemma 3.3 (No-case structure).** Suppose that `V₁^H ⊆ H ⊆ V₁` and `µ(G) < k/(C₀α)`. Then
`|V₁| ⩽ k/100` and `R_H < kα/100`.

Khanna–Mukhopadhyay–Shah, *Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation*, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), Lemma 3.3, p.21 (PDF 25), in the main case `k > α²` (§3.3, p.20) of the standing setup
(§3.2, p.19): `n^{1/3} ⩽ α ⩽ n^{1/2}`, `α ⩽ k ⩽ n`.

**Formalization Note** The source's standing "n sufficiently large" is not assumed. -/
theorem lemma_3_3 (n : ℕ) (α : ℝ) (k : ℕ) :
    (n : ℝ) ^ ((1 : ℝ) / 3) ≤ α → α ≤ (n : ℝ) ^ ((1 : ℝ) / 2) → α ≤ k → (k : ℝ) ≤ n → α ^ 2 < k →
    ∀ (G : AdjList n) (H : Finset (Fin n)), V1H G α k ⊆ H → H ⊆ V1 G α k →
      (TuranMatching.Clique.matchingNumber G.toGraph : ℝ) < k / (C0 * α) →
      ((V1 G α k).card : ℝ) ≤ k / 100 ∧ (RH G α k H : ℝ) < k * α / 100 := by sorry

end NAMatchEst
