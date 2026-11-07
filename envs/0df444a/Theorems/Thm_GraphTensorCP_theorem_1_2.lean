-- Prove2me | Theorems.Thm_GraphTensorCP_theorem_1_2
-- name    : GraphTensorCP.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:05:23.604374+00:00
-- url     : https://prove2.me/theorems/03dfd5df-1a04-4142-8112-3423be2aab24
-- title:
--   Theorem 1.2 — over every field, $\mathrm{MaxCut}(W)\le\log_2\tilde R_{\mathbb F}(\mathsf{WT}(Q))\le U^\Delta_{\mathrm{CP}}(W)$ for every weighted graph tensor
-- statement:
--   Let $\mathbb F$ be any field and let $Q$ be a symmetric $n\times n$ positive integer matrix, $n\ge2$, with all diagonal entries equal to $1$. Let $W$ be its logarithmic edge-weight matrix, $W_{i,j}=\log_2Q_{i,j}$. Then
--
--   $$\mathrm{MaxCut}(W)\le\log_2\tilde R_{\mathbb F}\big(\mathsf{WT}(Q)\big)\le U^\Delta_{\mathrm{CP}}(W).$$
--
--   Here $\mathsf{WT}(Q)$ is the weighted graph tensor with an edge of dimension $Q_{i,j}$ between legs $i$ and $j$, $\tilde R_{\mathbb F}$ is its asymptotic rank over $\mathbb F$, $\mathrm{MaxCut}(W)$ is the maximum total weight crossing a cut, and $U^\Delta_{\mathrm{CP}}(W)$ is the maximum of $\sum_{i<j}W_{i,j}P_{i,j}$ over symmetric nonnegative zero-diagonal $P$ with $J-2P$ copositive and $P_{i,j}\le P_{i,k}+P_{k,j}$ for distinct $i,j,k$.
--
--   This is the paper's main theorem. For $Q$ with entries $2$ on the edges of a graph $G$ it gives $\mathrm{MaxCut}(G)\le\log_2\tilde R_{\mathbb F}(\mathsf{GT}_2(G))\le U^\Delta_{\mathrm{CP}}(G)$, and for $G=K_3$ it contains $\omega\le9/4$ over every field.
--
--   **Formalization Note** The field is arbitrary (any universe). Copositivity is not positive semidefiniteness, and the path inequalities range over all distinct triples, edges or not.
--
--   Differences from the source:
--   - encoding: vertices $1,\dots,n$ → `Fin n` $=\{0,\dots,n-1\}$; reason: relabeling; same instances
--   - encoding: $\mathsf{WT}(Q)$ with leg $v$ of dimension $D_v$ indexed by the mixed-radix coordinate $I^Q_v(\lambda)$ → leg $v$ indexed by the tuple $(\lambda_{v,j})_j$ (`wt K Q`); reason: mixed radix is a bijection, so the tensors agree up to a permutation of coordinates within each leg, the paper's own identification (Definition 2.5)
--   - encoding: $\tilde R_{\mathbb F}(T)=\lim_N R_{\mathbb F}(T^{\otimes N})^{1/N}$ → `MME.tensorAsymptoticRank` $=\inf_{N\ge1}R(T^{\otimes N})^{1/N}$; reason: the paper proves the limit equals this infimum (p.19); both are $0$ at $T=0$
--   - encoding: $\max$ over nonempty proper $S$ → `maxCut`, a supremum over the finite nonempty index type of such $S$; reason: a supremum of finitely many values is their maximum
--   - encoding: $U^\Delta_{\mathrm{CP}}(W)$ as a maximum → `uCPDelta`, a real supremum of the feasible values; reason: the value set is nonempty and bounded and the maximum is attained (p.48), so the supremum is the maximum
-- source:
--   H. Zhou, Asymptotic Rank of Weighted Graph Tensors via Completely Positive Covers, arXiv:2610.34273 (version of 2026-11-03), Theorem 1.2, p.9 (restated as Theorem 5.6, eq. (15), p.48)

import Mathlib
import Definitions.Def_GraphTensorCP_IsDimMatrix
import Definitions.Def_GraphTensorCP_wt
import Definitions.Def_GraphTensorCP_maxCut
import Definitions.Def_GraphTensorCP_uCPDelta
import Definitions.Def_mme_tensor_rank

universe u

namespace GraphTensorCP

/-- **Theorem 1.2** (weighted graph tensors), Zhou, *Asymptotic Rank of Weighted Graph Tensors via Completely Positive Covers*, arXiv:2610.34273 (version of 2026-11-03), p.9 (restated as Theorem 5.6, eq. (15), p.48):
"Let F be any field and let Q be a symmetric n×n positive integer matrix, where n ≥ 2, with diagonal
entries equal to one. If W is its logarithmic edge-weight matrix, then
MaxCut(W) ≤ log₂ R̃_F(WT(Q)) ≤ U^Δ_CP(W). Here MaxCut(W) is the maximum total weight crossing a cut."

**Formalization Note.** `F` is any field `K` in any universe. `Q` is a dimension matrix
(`IsDimMatrix`), `W = logWeight Q` (`W_{i,j} = log₂ Q_{i,j}`), `WT(Q) = wt K Q` (product coordinates, the
paper's tensor up to coordinate permutations within legs), `R̃_F` is `MME.tensorAsymptoticRank`,
`MaxCut` is `maxCut` (Definition 2.27), and `U^Δ_CP` is `uCPDelta` (Definition 5.5): the copositive
program `J − 2P ∈ COP_n` (not PSD) with path inequalities over all distinct triples. -/
theorem theorem_1_2 {K : Type u} [Field K] {n : ℕ} (hn : 2 ≤ n) (Q : Matrix (Fin n) (Fin n) ℕ)
    (hQ : IsDimMatrix Q) :
    maxCut (logWeight Q) ≤ Real.logb 2 (MME.tensorAsymptoticRank (wt K Q)) ∧
      Real.logb 2 (MME.tensorAsymptoticRank (wt K Q)) ≤ uCPDelta (logWeight Q) := by sorry

end GraphTensorCP
