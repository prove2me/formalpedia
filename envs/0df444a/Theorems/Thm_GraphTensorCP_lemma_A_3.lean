-- Prove2me | Theorems.Thm_GraphTensorCP_lemma_A_3
-- name    : GraphTensorCP.lemma_A_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:05:19.425506+00:00
-- url     : https://prove2.me/theorems/2ee797d2-555a-4ba4-902a-d6706fb460a3
-- title:
--   Lemma A.3 — flattening across a weighted cut: $\mathrm{FR}_S(\mathsf{WT}(Q))=\prod_{|\{i,j\}\cap S|=1}Q_{i,j}=2^{\mathrm{cut}_W(S)}$
-- statement:
--   Let $Q$ be a dimension matrix of order $n\ge2$ with logarithmic edge-weight matrix $W$. For every nonempty proper subset $S\subsetneq\{1,\dots,n\}$, the rank of the flattening of $\mathsf{WT}(Q)$ that groups the legs in $S$ against the others is
--
--   $$\mathrm{FR}_S(\mathsf{WT}(Q))=\prod_{\substack{1\le i<j\le n\\|\{i,j\}\cap S|=1}}Q_{i,j}=2^{\mathrm{cut}_W(S)}.$$
--
--   In particular, for every finite simple graph $G$ on $\{1,\dots,n\}$ and every positive integer $q$, $\mathrm{FR}_S(\mathsf{GT}_q(G))=q^{|\delta_G(S)|}$, where $\delta_G(S)$ is the set of edges of $G$ with exactly one endpoint in $S$.
--
--   This flattening computation is the source of the maximum-cut lower bound on asymptotic rank.
--
--   **Formalization Note** $\mathrm{FR}_S$ is the published `MME.flatteningRank σ` with `σ : MME.Split (Fin n)` carrying the nonempty proper set $S$; it is the rank of the flattening map, i.e. the matrix rank of $\mathrm{Flat}_S$. Edges of $\delta_G(S)$ are counted as pairs $i<j$.
--
--   Differences from the source:
--   - encoding: vertices $1,\dots,n$ → `Fin n` $=\{0,\dots,n-1\}$; reason: relabeling; same instances
--   - encoding: $\mathsf{WT}(Q)$ with leg $v$ of dimension $D_v$ indexed by the mixed-radix coordinate $I^Q_v(\lambda)$ → leg $v$ indexed by the tuple $(\lambda_{v,j})_j$ (`wt K Q`); reason: mixed radix is a bijection, so the tensors agree up to a permutation of coordinates within each leg, the paper's own identification (Definition 2.5)
--   - encoding: $\mathrm{FR}_S$ = matrix rank of $\mathrm{Flat}_S$ (Definition A.1) → `MME.flatteningRank σ`, the rank of the linear map $(\bigotimes_{v\in S}V_v)^*\to\bigotimes_{v\notin S}V_v$; reason: this linear map has matrix $\mathrm{Flat}_S$; same rank
-- source:
--   H. Zhou, Asymptotic Rank of Weighted Graph Tensors via Completely Positive Covers, arXiv:2610.34273 (version of 2026-11-03), Lemma A.3, p.74

import Mathlib
import Definitions.Def_GraphTensorCP_IsDimMatrix
import Definitions.Def_GraphTensorCP_wt
import Definitions.Def_GraphTensorCP_maxCut
import Definitions.Def_mme_flattening

universe u

namespace GraphTensorCP

/-- **Lemma A.3** (flattening across a weighted cut), Zhou, *Asymptotic Rank of Weighted Graph Tensors via Completely Positive Covers*, arXiv:2610.34273 (version of 2026-11-03), p.74:
"Let Q be a dimension matrix of order n ≥ 2 with logarithmic edge-weight matrix W. For every
nonempty proper subset S ⊂ {1, . . . , n}, FR_S(WT(Q)) = ∏_{1≤i<j≤n, |{i,j}∩S|=1} Q_{i,j} = 2^{cut_W(S)}.
In particular, FR_S(GT_q(G)) = q^{|δ_G(S)|} for every positive integer q."

**Formalization Note.** `FR_S` is the published `MME.flatteningRank σ`, where `σ : MME.Split (Fin n)`
packages a nonempty proper subset `σ.S`; it is the rank of the flattening map
`(⊗_{v∈S} V_v)^* → ⊗_{v∉S} V_v`, i.e. the matrix rank of `Flat_S` (Definition A.1). `|{i,j} ∩ S| = 1` is
`i ∈ S ↔ j ∉ S`. `δ_G(S)` is counted as the pairs `i < j` that are edges of `G` crossing `S`. -/
theorem lemma_A_3 {K : Type u} [Field K] {n : ℕ} (hn : 1 < n) (Q : Matrix (Fin n) (Fin n) ℕ)
    (hQ : IsDimMatrix Q) (σ : MME.Split (Fin n)) :
    MME.flatteningRank σ (wt K Q) =
        (∏ i, ∏ j, if i < j ∧ (i ∈ σ.S ↔ j ∉ σ.S) then Q i j else 1) ∧
      (MME.flatteningRank σ (wt K Q) : ℝ) = (2 : ℝ) ^ cutWeight (logWeight Q) σ.S ∧
      ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (q : ℕ), 0 < q →
        MME.flatteningRank σ (wt K (graphDim G q)) =
          q ^ (Finset.univ.filter (fun p : Fin n × Fin n =>
            p.1 < p.2 ∧ G.Adj p.1 p.2 ∧ (p.1 ∈ σ.S ↔ p.2 ∉ σ.S))).card := by sorry

end GraphTensorCP
