-- Prove2me | Theorems.Thm_GraphTensorCP_Supplement_theorem_5_6
-- name    : GraphTensorCP.Supplement.theorem_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T04:25:14.716868+00:00
-- url     : https://prove2.me/theorems/7d430e38-47ea-4313-ab14-20b57a2df463
-- title:
--   Theorem 5.6 — full weighted graph tensor bound
-- statement:
--   Let $\mathbb F$ be any field, $n\ge2$, and let $Q$ be a dimension matrix with logarithmic edge-weight matrix $W=\log_2Q$. Then
--
--   $$
--   \mathrm{MaxCut}(W)\le\log_2\widetilde R_{\mathbb F}(\mathsf{WT}(Q))\le U^\Delta_{\mathrm{CP}}(W).
--   $$
--
--   More generally, for every real symmetric nonnegative zero-diagonal weight matrix $W$,
--
--   $$
--   \mathrm{MaxCut}(W)\le\Gamma_{\mathbb F}(W)\le U^\Delta_{\mathrm{CP}}(W)
--   \le U_{\mathrm{CP}}(W)\le\sum_{i<j}W_{i,j}.
--   $$
--
--   In particular, every finite simple graph $G$ on $n$ vertices satisfies
--
--   $$
--   \mathrm{MaxCut}(G)\le\log_2\widetilde R_{\mathbb F}(\mathsf{GT}_2(G))\le U^\Delta_{\mathrm{CP}}(G).
--   $$
--
--   This is the paper’s complete weighted theorem, including the real-weight extension, both conic comparisons, and the graph specialization.
--
--   **Formalization Note** Graphs use vertex type `Fin n`; `graphDim G 2` builds $\mathsf{GT}_2(G)$. Maxima and minima in the conic definitions are represented by suprema and infima on feasible sets whose attainment is proved in the paper.
--
--   Differences from the source:
--   - encoding: the source indexes vertices by $1,\ldots,n$ and uses mixed-radix coordinates for $\mathsf{WT}(Q)$ → Lean uses `Fin n` and the published product-coordinate tensor `wt`; reason: the coordinates are related by a mode-wise basis permutation, so every tensor instance is unchanged.
--   - encoding: the source writes attained maxima and minima → Lean uses real suprema and infima over the identical feasible sets; reason: the source proves nonemptiness, boundedness, and attainment, so the values agree.
-- source:
--   Zhou, Asymptotic Rank of Weighted Graph Tensors via Completely Positive Covers, arXiv:2610.34273 (version of 2026-11-03), Theorem 5.6, pp.48–49

import Mathlib
import Definitions.Def_GraphTensorCP_IsDimMatrix
import Definitions.Def_GraphTensorCP_wt
import Definitions.Def_GraphTensorCP_maxCut
import Definitions.Def_GraphTensorCP_uCPDelta
import Definitions.Def_GraphTensorCP_specWeight
import Definitions.Def_GraphTensorCP_Supplement_uCP
import Definitions.Def_mme_tensor_rank

universe u

namespace GraphTensorCP

namespace Supplement

/-- **Theorem 5.6 (weighted graph tensor bound)**, Zhou, *Asymptotic Rank of Weighted Graph
Tensors via Completely Positive Covers*, arXiv:2610.34273 (version of 2026-11-03), pp.48–49.
This statement includes all four clauses: equation (15), the real-weight `Γ_F` extension, the
comparison `U^Δ_CP ≤ U_CP ≤ ΣW`, and the ordinary-graph specialization (16).

**Formalization Note.** `K` is an arbitrary field in any universe. Weight matrices are explicitly
required to be symmetric, nonnegative, and zero-diagonal through `IsWeightMatrix`. Graphs have
vertex type `Fin n`; `graphDim G 2` is the dimension matrix of `GT₂(G)`. All sums are over
unordered pairs. -/
theorem theorem_5_6 {K : Type u} [Field K] {n : ℕ} (hn : 2 ≤ n)
    (Q : Matrix (Fin n) (Fin n) ℕ) (hQ : IsDimMatrix Q)
    (W : Matrix (Fin n) (Fin n) ℝ) (hW : IsWeightMatrix W)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (maxCut (logWeight Q) ≤ Real.logb 2 (MME.tensorAsymptoticRank (wt K Q)) ∧
      Real.logb 2 (MME.tensorAsymptoticRank (wt K Q)) ≤ uCPDelta (logWeight Q)) ∧
    (maxCut W ≤ gammaF K (by omega) W ∧ gammaF K (by omega) W ≤ uCPDelta W) ∧
    (uCPDelta W ≤ uCP W ∧
      uCP W ≤ ∑ i, ∑ j, if i < j then W i j else 0) ∧
    (maxCut (G.adjMatrix ℝ) ≤
        Real.logb 2 (MME.tensorAsymptoticRank (wt K (graphDim G 2))) ∧
      Real.logb 2 (MME.tensorAsymptoticRank (wt K (graphDim G 2))) ≤
        uCPDelta (G.adjMatrix ℝ)) := by sorry

end Supplement

end GraphTensorCP
