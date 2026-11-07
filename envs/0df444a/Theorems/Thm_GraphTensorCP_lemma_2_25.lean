-- Prove2me | Theorems.Thm_GraphTensorCP_lemma_2_25
-- name    : GraphTensorCP.lemma_2_25
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:05:52.837729+00:00
-- url     : https://prove2.me/theorems/2d60b1ee-9cd5-4c0b-8c7f-a6b9828517e0
-- title:
--   Lemma 2.25 — spectral values of weighted graph tensors: $\phi(\mathsf{WT}(Q))=2^{\sum_{i<j}W_{i,j}P^{(\phi)}_{i,j}}$, $0\le P^{(\phi)}\le1$, star inequality
-- statement:
--   Let $n\ge2$, let $\phi\in\Phi_{n,\mathbb F}$ and let $P^{(\phi)}$ be its spectral edge-weight matrix. Then:
--
--   1. for $1\le i<j\le n$: $0\le P^{(\phi)}_{i,j}\le1$;
--   2. for $1\le i<j\le n$ and every positive integer $q$: $\phi(E^{(q)}_{i,j})=q^{P^{(\phi)}_{i,j}}$;
--   3. for every dimension matrix $Q$ with logarithmic edge-weight matrix $W$:
--   $$\phi(\mathsf{WT}(Q))=\prod_{1\le i<j\le n}Q_{i,j}^{P^{(\phi)}_{i,j}}=2^{\sum_{1\le i<j\le n}W_{i,j}P^{(\phi)}_{i,j}};$$
--   4. for every simple graph $G$ on $\{1,\dots,n\}$ and every positive integer $q$: $\phi(\mathsf{GT}_q(G))=q^{\sum_{(i,j)\in E(G)}P^{(\phi)}_{i,j}}$;
--   5. (star inequality) $\sum_{j=2}^{n}P^{(\phi)}_{1,j}\ge1$.
--
--   A spectral point is thus determined on all weighted graph tensors by the $\binom n2$ numbers $P^{(\phi)}_{i,j}$, which makes $\log_2\phi(\mathsf{WT}(Q))$ linear in $W$.
--
--   **Formalization Note** Vertex $1$ of the star inequality is index $0$, and the sum runs over $j>0$. Edges $(i,j)\in E(G)$ are the pairs $i<j$ adjacent in $G$. Real powers are `Real.rpow`.
--
--   Differences from the source:
--   - encoding: vertices $1,\dots,n$ → `Fin n` $=\{0,\dots,n-1\}$; reason: relabeling; same instances
--   - encoding: $\mathsf{WT}(Q)$ with leg $v$ of dimension $D_v$ indexed by the mixed-radix coordinate $I^Q_v(\lambda)$ → leg $v$ indexed by the tuple $(\lambda_{v,j})_j$ (`wt K Q`); reason: mixed radix is a bijection, so the tensors agree up to a permutation of coordinates within each leg, the paper's own identification (Definition 2.5)
--   - encoding: spectral points $\phi:\mathrm{Tens}_n(\mathbb F)\to\mathbb R_{\ge0}$ (Definition 2.19) → monotone semiring homomorphisms on the published quotient `MME.TensorQ` by mutual restriction (`Spec K n hn`); reason: a spectral point is constant on mutual-restriction classes and its four conditions are exactly "monotone semiring homomorphism"; same set of maps
--   - encoding: $E^{(q)}_{i,j}$ in coordinates → `edgeTensor K i j q` $=\mathsf{WT}$ of the single-edge dimension matrix; reason: same tensor up to coordinates within legs
-- source:
--   H. Zhou, Asymptotic Rank of Weighted Graph Tensors via Completely Positive Covers, arXiv:2610.34273 (version of 2026-11-03), Lemma 2.25, p.24

import Mathlib
import Definitions.Def_GraphTensorCP_IsDimMatrix
import Definitions.Def_GraphTensorCP_wt
import Definitions.Def_GraphTensorCP_specWeight

universe u

namespace GraphTensorCP

/-- **Lemma 2.25** (spectral values of weighted graph tensors), Zhou, *Asymptotic Rank of Weighted Graph Tensors via Completely Positive Covers*, arXiv:2610.34273 (version of 2026-11-03), p.24:
"Let n ≥ 2, let ϕ ∈ Φ_{n,F}, and let P^{(ϕ)} be its spectral edge-weight matrix. For 1 ≤ i < j ≤ n and
every positive integer q, 0 ≤ P^{(ϕ)}_{i,j} ≤ 1, ϕ(E^{(q)}_{i,j}) = q^{P^{(ϕ)}_{i,j}}. For every dimension matrix Q
with logarithmic edge-weight matrix W, ϕ(WT(Q)) = ∏_{1≤i<j≤n} Q_{i,j}^{P^{(ϕ)}_{i,j}} =
2^{Σ_{1≤i<j≤n} W_{i,j}P^{(ϕ)}_{i,j}}. Consequently, for every simple graph G on [n] and every positive
integer q, ϕ(GT_q(G)) = q^{Σ_{(i,j)∈E(G)} P^{(ϕ)}_{i,j}}. Moreover, Σ_{j=2}^{n} P^{(ϕ)}_{1,j} ≥ 1."

**Formalization Note.** Vertices are `Fin n`; the paper's vertex `1` is index `0`, so the star
inequality sums `P^{(ϕ)}_{0,j}` over `j > 0`. Real powers are `Real.rpow`. Edges `(i, j)` of `G` are
the pairs `i < j` with `G.Adj i j`. -/
theorem lemma_2_25 {K : Type u} [Field K] {n : ℕ} (hn : 1 < n) (φ : Spec K n hn) :
    (∀ i j : Fin n, i < j → 0 ≤ specWeight φ i j ∧ specWeight φ i j ≤ 1) ∧
    (∀ i j : Fin n, i < j → ∀ q : ℕ, 0 < q →
      φ (MME.TensorQ.toQ (edgeTensor K i j q)) = (q : ℝ) ^ specWeight φ i j) ∧
    (∀ Q : Matrix (Fin n) (Fin n) ℕ, IsDimMatrix Q →
      φ (MME.TensorQ.toQ (wt K Q)) =
          (∏ i, ∏ j, if i < j then (Q i j : ℝ) ^ specWeight φ i j else 1) ∧
        φ (MME.TensorQ.toQ (wt K Q)) =
          (2 : ℝ) ^ (∑ i, ∑ j, if i < j then logWeight Q i j * specWeight φ i j else 0)) ∧
    (∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (q : ℕ), 0 < q →
      φ (MME.TensorQ.toQ (wt K (graphDim G q))) =
        (q : ℝ) ^ (∑ i, ∑ j, if i < j ∧ G.Adj i j then specWeight φ i j else 0)) ∧
    1 ≤ ∑ j : Fin n, if (⟨0, by omega⟩ : Fin n) < j then specWeight φ ⟨0, by omega⟩ j else 0 := by sorry

end GraphTensorCP
