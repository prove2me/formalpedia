-- Prove2me | Theorems.Thm_GraphTensorCP_lemma_2_28
-- name    : GraphTensorCP.lemma_2_28
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:06:03.091206+00:00
-- url     : https://prove2.me/theorems/f213b03f-b509-45d0-820f-2bb62d94b19a
-- title:
--   Lemma 2.28 — weighted spectral formula $\Gamma_{\mathbb F}(W)=\log_2\tilde R_{\mathbb F}(\mathsf{WT}(Q))$ and analytic properties of $\Gamma_{\mathbb F}$
-- statement:
--   For every dimension matrix $Q$ of order $n\ge2$ with logarithmic edge-weight matrix $W$,
--
--   $$\Gamma_{\mathbb F}(W)=\log_2\tilde R_{\mathbb F}(\mathsf{WT}(Q)).\qquad(2)$$
--
--   In particular, $\Gamma_{\mathbb F}(G)=\log_2\tilde R_{\mathbb F}(\mathsf{GT}_2(G))$ for every simple graph $G$ on $\{1,\dots,n\}$. On nonnegative weight matrices (symmetric, nonnegative, zero diagonal), $\Gamma_{\mathbb F}$ is
--
--   1. monotone: $W\le W'$ entrywise implies $\Gamma_{\mathbb F}(W)\le\Gamma_{\mathbb F}(W')$;
--   2. convex;
--   3. positively homogeneous: $\Gamma_{\mathbb F}(cW)=c\,\Gamma_{\mathbb F}(W)$ for $c\ge0$;
--   4. subadditive: $\Gamma_{\mathbb F}(W+W')\le\Gamma_{\mathbb F}(W)+\Gamma_{\mathbb F}(W')$;
--
--   and moreover
--
--   $$|\Gamma_{\mathbb F}(W)-\Gamma_{\mathbb F}(W')|\le\sum_{1\le i<j\le n}|W_{i,j}-W'_{i,j}|.\qquad(3)$$
--
--   Identity (2) reduces the goal's upper bound to a bound on $\sum_{i<j}W_{i,j}P^{(\phi)}_{i,j}$ for each spectral point.
--
--   **Formalization Note** Convexity is `ConvexOn ℝ` on the convex cone of nonnegative weight matrices.
--
--   Differences from the source:
--   - encoding: vertices $1,\dots,n$ → `Fin n` $=\{0,\dots,n-1\}$; reason: relabeling; same instances
--   - encoding: $\mathsf{WT}(Q)$ with leg $v$ of dimension $D_v$ indexed by the mixed-radix coordinate $I^Q_v(\lambda)$ → leg $v$ indexed by the tuple $(\lambda_{v,j})_j$ (`wt K Q`); reason: mixed radix is a bijection, so the tensors agree up to a permutation of coordinates within each leg, the paper's own identification (Definition 2.5)
--   - encoding: $\tilde R_{\mathbb F}(T)=\lim_N R_{\mathbb F}(T^{\otimes N})^{1/N}$ → `MME.tensorAsymptoticRank` $=\inf_{N\ge1}R(T^{\otimes N})^{1/N}$; reason: the paper proves the limit equals this infimum (p.19); both are $0$ at $T=0$
--   - encoding: $\Gamma_{\mathbb F}(W)$ as a maximum over $\Phi_{n,\mathbb F}$ → `gammaF`, a real supremum; reason: the family is bounded (Lemma 2.25) and the maximum is attained (p.25)
--   - generalization: positively homogeneous ($c>0$) → $\Gamma_{\mathbb F}(cW)=c\,\Gamma_{\mathbb F}(W)$ for every $c\ge0$; reason: also covers $c=0$, where it says $\Gamma_{\mathbb F}(0)=0$; specializes to the $c>0$ statement
-- source:
--   H. Zhou, Asymptotic Rank of Weighted Graph Tensors via Completely Positive Covers, arXiv:2610.34273 (version of 2026-11-03), Lemma 2.28, p.26

import Mathlib
import Definitions.Def_GraphTensorCP_IsDimMatrix
import Definitions.Def_GraphTensorCP_wt
import Definitions.Def_GraphTensorCP_specWeight
import Definitions.Def_mme_tensor_rank

universe u

namespace GraphTensorCP

/-- **Lemma 2.28** (weighted spectral formula), Zhou, *Asymptotic Rank of Weighted Graph Tensors via Completely Positive Covers*, arXiv:2610.34273 (version of 2026-11-03), p.26:
"For every dimension matrix Q with logarithmic edge-weight matrix W, Γ_F(W) = log₂ R̃_F(WT(Q)). (2)
In particular, Γ_F(G) = log₂ R̃_F(GT₂(G)). On nonnegative weight matrices, Γ_F is monotone, convex,
positively homogeneous, and subadditive. Moreover, |Γ_F(W) − Γ_F(W′)| ≤ Σ_{1≤i<j≤n} |W_{i,j} − W′_{i,j}|. (3)"

**Formalization Note.** "Nonnegative weight matrices" are `IsWeightMatrix` (symmetric, zero
diagonal, nonnegative: the domain of `Γ_F` in Definition 2.26), a convex cone. Monotone is for the
entrywise order; positive homogeneity is stated for every `c ≥ 0` (it includes `c = 0`). `Γ_F(G)`
is `gammaF K hn (G.adjMatrix ℝ)` and `GT₂(G) = wt K (graphDim G 2)`. -/
theorem lemma_2_28 {K : Type u} [Field K] {n : ℕ} (hn : 1 < n) :
    (∀ Q : Matrix (Fin n) (Fin n) ℕ, IsDimMatrix Q →
      gammaF K hn (logWeight Q) = Real.logb 2 (MME.tensorAsymptoticRank (wt K Q))) ∧
    (∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      gammaF K hn (G.adjMatrix ℝ) =
        Real.logb 2 (MME.tensorAsymptoticRank (wt K (graphDim G 2)))) ∧
    (∀ W W' : Matrix (Fin n) (Fin n) ℝ, IsWeightMatrix W → IsWeightMatrix W' →
      (∀ i j, W i j ≤ W' i j) → gammaF K hn W ≤ gammaF K hn W') ∧
    ConvexOn ℝ {W : Matrix (Fin n) (Fin n) ℝ | IsWeightMatrix W} (gammaF K hn) ∧
    (∀ W : Matrix (Fin n) (Fin n) ℝ, IsWeightMatrix W → ∀ c : ℝ, 0 ≤ c →
      gammaF K hn (c • W) = c * gammaF K hn W) ∧
    (∀ W W' : Matrix (Fin n) (Fin n) ℝ, IsWeightMatrix W → IsWeightMatrix W' →
      gammaF K hn (W + W') ≤ gammaF K hn W + gammaF K hn W') ∧
    (∀ W W' : Matrix (Fin n) (Fin n) ℝ, IsWeightMatrix W → IsWeightMatrix W' →
      |gammaF K hn W - gammaF K hn W'| ≤ ∑ i, ∑ j, if i < j then |W i j - W' i j| else 0) := by sorry

end GraphTensorCP
