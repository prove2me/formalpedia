-- Prove2me | Theorems.Thm_GraphTensorCP_theorem_4_10
-- name    : GraphTensorCP.theorem_4_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:05:00.972219+00:00
-- url     : https://prove2.me/theorems/f6f4231d-2f28-4fe2-a78f-54af9ecf0dce
-- title:
--   Theorem 4.10 (= Theorem 1.1) — complete graph bound $\lfloor n^2/4\rfloor\le\log_2\tilde R_{\mathbb F}(\mathsf{GT}_2(K_n))\le n^2/4$
-- statement:
--   For every field $\mathbb F$ and every integer $n\ge2$,
--
--   $$\Big\lfloor\frac{n^2}{4}\Big\rfloor\le\log_2\tilde R_{\mathbb F}\big(\mathsf{GT}_2(K_n)\big)\le\frac{n^2}{4}.$$
--
--   Here $\mathsf{GT}_2(K_n)$ is the graph tensor of the complete graph with binary edges. For $n=3$ this is the matrix multiplication tensor and the upper bound reads $\omega\le 9/4$ over every field; for even $n$ the two bounds coincide. This is the paper's first main result (Theorem 1.1, p.4) and the engine of the weighted bound.
--
--   **Formalization Note** $\lfloor n^2/4\rfloor$ is the natural-number quotient `n ^ 2 / 4`; $\mathsf{GT}_2(K_n)$ is `wt K (graphDim ⊤ 2)`.
--
--   Differences from the source:
--   - encoding: vertices $1,\dots,n$ → `Fin n` $=\{0,\dots,n-1\}$; reason: relabeling; same instances
--   - encoding: $\mathsf{WT}(Q)$ with leg $v$ of dimension $D_v$ indexed by the mixed-radix coordinate $I^Q_v(\lambda)$ → leg $v$ indexed by the tuple $(\lambda_{v,j})_j$ (`wt K Q`); reason: mixed radix is a bijection, so the tensors agree up to a permutation of coordinates within each leg, the paper's own identification (Definition 2.5)
--   - encoding: $\tilde R_{\mathbb F}(T)=\lim_N R_{\mathbb F}(T^{\otimes N})^{1/N}$ → `MME.tensorAsymptoticRank` $=\inf_{N\ge1}R(T^{\otimes N})^{1/N}$; reason: the paper proves the limit equals this infimum (p.19); both are $0$ at $T=0$
-- source:
--   H. Zhou, Asymptotic Rank of Weighted Graph Tensors via Completely Positive Covers, arXiv:2610.34273 (version of 2026-11-03), Theorem 4.10, p.43 (= Theorem 1.1, p.4)

import Mathlib
import Definitions.Def_GraphTensorCP_wt
import Definitions.Def_mme_tensor_rank

universe u

namespace GraphTensorCP

/-- **Theorem 4.10** (complete graph bound; = Theorem 1.1, p.4), Zhou, *Asymptotic Rank of Weighted Graph Tensors via Completely Positive Covers*, arXiv:2610.34273 (version of 2026-11-03), p.43:
"For every field F and every integer n ≥ 2, ⌊n²/4⌋ ≤ log₂ R̃_F(GT₂(K_n)) ≤ n²/4."

**Formalization Note.** `GT₂(K_n) = wt K (graphDim ⊤ 2)` (every pair an edge of dimension 2);
`R̃_F` is `MME.tensorAsymptoticRank`, `log₂` is `Real.logb 2`, and `⌊n²/4⌋` is the natural-number
quotient `n ^ 2 / 4`. -/
theorem theorem_4_10 {K : Type u} [Field K] {n : ℕ} (hn : 2 ≤ n) :
    ((n ^ 2 / 4 : ℕ) : ℝ) ≤
        Real.logb 2 (MME.tensorAsymptoticRank (wt K (graphDim (⊤ : SimpleGraph (Fin n)) 2))) ∧
      Real.logb 2 (MME.tensorAsymptoticRank (wt K (graphDim (⊤ : SimpleGraph (Fin n)) 2))) ≤
        (n : ℝ) ^ 2 / 4 := by sorry

end GraphTensorCP
