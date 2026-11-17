-- Prove2me | Theorems.Thm_GraphTensorCP_Supplement_theorem_6_10
-- name    : GraphTensorCP.Supplement.theorem_6_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T04:26:24.29502+00:00
-- url     : https://prove2.me/theorems/0e91de5e-e34c-4b07-b7cb-be6c6bf787b9
-- title:
--   Theorem 6.10 — complete multipartite bounds
-- statement:
--   Let $\mathbb F$ be any field, $k\ge2$, and let $s_1,\ldots,s_k$ be positive integers. Put
--
--   $$
--   N=\sum_i s_i,\qquad b=\max_i s_i,\qquad
--   \delta=\min_{S\subseteq[k]}\left|N-2\sum_{i\in S}s_i\right|.
--   $$
--
--   For $G=K_{s_1,\ldots,s_k}$,
--
--   $$
--   \mathrm{MaxCut}(G)=\frac{N^2-\delta^2}{4}
--   \le\Gamma_{\mathbb F}(G)\le U_{\mathrm{CP}}(G),
--   $$
--
--   and
--
--   $$
--   U_{\mathrm{CP}}(G)=
--   \begin{cases}
--   b(N-b),&b\ge N/2,\\
--   N^2/4,&b\le N/2.
--   \end{cases}
--   $$
--
--   The exponent equals the maximum cut whenever $b\ge N/2$ or $\delta=0$.
--
--   Differences from the source:
--   - encoding: the source uses named independent parts and vertices $1,\ldots,N$ → Lean transports Mathlib’s complete multipartite graph on part-position pairs to `Fin N`; reason: the transport is a graph isomorphism and preserves every displayed quantity.
--   - encoding: the source writes $b\ge N/2$ and $b\le N/2$ → Lean writes $N\le2b$ and $2b\le N$; reason: the variables are nonnegative integers and the conditions are equivalent without division.
-- source:
--   Zhou, Asymptotic Rank of Weighted Graph Tensors via Completely Positive Covers, arXiv:2610.34273 (version of 2026-11-03), Theorem 6.10, pp.62–63

import Mathlib
import Definitions.Def_GraphTensorCP_maxCut
import Definitions.Def_GraphTensorCP_specWeight
import Definitions.Def_GraphTensorCP_Supplement_uCP
import Definitions.Def_GraphTensorCP_Supplement_completeMultipartiteGraph

universe u

namespace GraphTensorCP

namespace Supplement

/-- **Theorem 6.10 (complete multipartite bounds)**, Zhou, *Asymptotic Rank of Weighted Graph
Tensors via Completely Positive Covers*, arXiv:2610.34273 (version of 2026-11-03), pp.62–63.
The maximum cut is exact, `U_CP` has both stated branches, and the exponent equals the maximum
cut in either of the two regimes from the paper.

**Formalization Note.** Parts are indexed by `Fin k`, all sizes are positive,
`N = Σ_i s_i`, `b = sup_i s_i` (the maximum on the nonempty finite index set), and `δ` is
`partitionImbalance s`. The conditions `b ≥ N/2` and `b ≤ N/2` are written without division as
`N ≤ 2b` and `2b ≤ N`. Natural subtraction in `b*(N-b)` is safe because `b` is a part size and
therefore at most `N`. -/
theorem theorem_6_10 {K : Type u} [Field K] {k : ℕ} (hk : 2 ≤ k) (s : Fin k → ℕ)
    (hs : ∀ i, 0 < s i) :
    let N := ∑ i, s i
    let b := Finset.univ.sup s
    let delta := partitionImbalance s
    let G := completeMultipartiteGraph s
    maxCut (G.adjMatrix ℝ) = ((N : ℝ) ^ 2 - (delta : ℝ) ^ 2) / 4 ∧
    ((N : ℝ) ^ 2 - (delta : ℝ) ^ 2) / 4 ≤
      gammaF K (totalSize_gt_one hk s hs) (G.adjMatrix ℝ) ∧
    gammaF K (totalSize_gt_one hk s hs) (G.adjMatrix ℝ) ≤ uCP (G.adjMatrix ℝ) ∧
    (N ≤ 2 * b → uCP (G.adjMatrix ℝ) = (b : ℝ) * (N - b : ℕ)) ∧
    (2 * b ≤ N → uCP (G.adjMatrix ℝ) = (N : ℝ) ^ 2 / 4) ∧
    ((N ≤ 2 * b ∨ delta = 0) →
      gammaF K (totalSize_gt_one hk s hs) (G.adjMatrix ℝ) = maxCut (G.adjMatrix ℝ)) := by sorry

end Supplement

end GraphTensorCP
