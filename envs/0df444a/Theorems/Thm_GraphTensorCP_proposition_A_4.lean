-- Prove2me | Theorems.Thm_GraphTensorCP_proposition_A_4
-- name    : GraphTensorCP.proposition_A_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:05:46.63062+00:00
-- url     : https://prove2.me/theorems/7bc4aa2f-d7a3-4c2d-a444-35b0e286cbc3
-- title:
--   Proposition A.4 — weighted maximum-cut lower bound $\mathrm{MaxCut}(W)\le\log_2\tilde R_{\mathbb F}(\mathsf{WT}(Q))$, equality for bipartite support
-- statement:
--   For every field $\mathbb F$ and every dimension matrix $Q$ of order $n\ge2$ with logarithmic edge-weight matrix $W$,
--
--   $$\mathrm{MaxCut}(W)\le\log_2\tilde R_{\mathbb F}(\mathsf{WT}(Q)).$$
--
--   If the support graph of $W$ is bipartite, then
--
--   $$\log_2\tilde R_{\mathbb F}(\mathsf{WT}(Q))=\mathrm{MaxCut}(W)=\sum_{1\le i<j\le n}W_{i,j}.$$
--
--   Consequently:
--
--   1. $\Gamma_{\mathbb F}(G)\ge\mathrm{MaxCut}(G)$ for every simple graph $G$ on $\{1,\dots,n\}$;
--   2. $\Gamma_{\mathbb F}(G)=\mathrm{MaxCut}(G)$ when $G$ is bipartite;
--   3. $\Gamma_{\mathbb F}(K_n)\ge\lfloor n^2/4\rfloor$.
--
--   Here $\tilde R_{\mathbb F}$ is the asymptotic rank and $\Gamma_{\mathbb F}(G)=\Gamma_{\mathbb F}(A_G)$ the weighted graph exponent of the adjacency matrix. This is the lower half of the mission's goal, together with its exact bipartite case.
--
--   **Formalization Note** "Bipartite" is `SimpleGraph.Colorable 2`. $\lfloor n^2/4\rfloor$ is the natural-number quotient `n ^ 2 / 4`. $K_n$ is the complete graph `⊤`.
--
--   Differences from the source:
--   - encoding: vertices $1,\dots,n$ → `Fin n` $=\{0,\dots,n-1\}$; reason: relabeling; same instances
--   - encoding: $\mathsf{WT}(Q)$ with leg $v$ of dimension $D_v$ indexed by the mixed-radix coordinate $I^Q_v(\lambda)$ → leg $v$ indexed by the tuple $(\lambda_{v,j})_j$ (`wt K Q`); reason: mixed radix is a bijection, so the tensors agree up to a permutation of coordinates within each leg, the paper's own identification (Definition 2.5)
--   - encoding: $\tilde R_{\mathbb F}(T)=\lim_N R_{\mathbb F}(T^{\otimes N})^{1/N}$ → `MME.tensorAsymptoticRank` $=\inf_{N\ge1}R(T^{\otimes N})^{1/N}$; reason: the paper proves the limit equals this infimum (p.19); both are $0$ at $T=0$
--   - encoding: $\max$ over nonempty proper $S$ → `maxCut`, a supremum over the finite nonempty index type of such $S$; reason: a supremum of finitely many values is their maximum
--   - encoding: $\Gamma_{\mathbb F}(W)$ as a maximum over $\Phi_{n,\mathbb F}$ → `gammaF`, a real supremum; reason: the family is bounded (Lemma 2.25) and the maximum is attained (p.25)
--   - encoding: bipartite → `SimpleGraph.Colorable 2`; reason: a graph is bipartite iff it is 2-colorable; same instances
-- source:
--   H. Zhou, Asymptotic Rank of Weighted Graph Tensors via Completely Positive Covers, arXiv:2610.34273 (version of 2026-11-03), Proposition A.4, p.75

import Mathlib
import Definitions.Def_GraphTensorCP_IsDimMatrix
import Definitions.Def_GraphTensorCP_wt
import Definitions.Def_GraphTensorCP_maxCut
import Definitions.Def_GraphTensorCP_specWeight
import Definitions.Def_mme_tensor_rank

universe u

namespace GraphTensorCP

/-- **Proposition A.4** (weighted maximum-cut lower bound), Zhou, *Asymptotic Rank of Weighted Graph Tensors via Completely Positive Covers*, arXiv:2610.34273 (version of 2026-11-03), p.75:
"For every field F and every dimension matrix Q of order n ≥ 2 with logarithmic edge-weight matrix
W, MaxCut(W) ≤ log₂ R̃_F(WT(Q)). If the support graph of W is bipartite, then
log₂ R̃_F(WT(Q)) = MaxCut(W) = Σ_{1≤i<j≤n} W_{i,j}. Consequently, Γ_F(G) ≥ MaxCut(G) for every simple
graph G, with equality for bipartite G, and Γ_F(K_n) ≥ ⌊n²/4⌋."

**Formalization Note.** `R̃_F` is `MME.tensorAsymptoticRank`, `log₂` is `Real.logb 2`. "Bipartite" is
`SimpleGraph.Colorable 2` (of the support graph, resp. of `G`). `Γ_F(G) = Γ_F(A_G)` with
`A_G = G.adjMatrix ℝ`, `MaxCut(G) = MaxCut(A_G)` (Definitions 2.26–2.27), and `K_n` is `⊤`.
`⌊n²/4⌋` is the natural-number quotient `n ^ 2 / 4`. -/
theorem proposition_A_4 {K : Type u} [Field K] {n : ℕ} (hn : 1 < n) :
    (∀ Q : Matrix (Fin n) (Fin n) ℕ, IsDimMatrix Q →
      maxCut (logWeight Q) ≤ Real.logb 2 (MME.tensorAsymptoticRank (wt K Q)) ∧
      ((supportGraph (logWeight Q)).Colorable 2 →
        Real.logb 2 (MME.tensorAsymptoticRank (wt K Q)) = maxCut (logWeight Q) ∧
        maxCut (logWeight Q) = ∑ i, ∑ j, if i < j then logWeight Q i j else 0)) ∧
    (∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      maxCut (G.adjMatrix ℝ) ≤ gammaF K hn (G.adjMatrix ℝ) ∧
      (G.Colorable 2 → gammaF K hn (G.adjMatrix ℝ) = maxCut (G.adjMatrix ℝ))) ∧
    ((n ^ 2 / 4 : ℕ) : ℝ) ≤ gammaF K hn ((⊤ : SimpleGraph (Fin n)).adjMatrix ℝ) := by sorry

end GraphTensorCP
