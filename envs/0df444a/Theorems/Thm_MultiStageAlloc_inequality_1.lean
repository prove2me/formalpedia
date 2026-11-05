-- Prove2me | Theorems.Thm_MultiStageAlloc_inequality_1
-- name    : MultiStageAlloc.inequality_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:34:08.98334+00:00
-- url     : https://prove2.me/theorems/51d8566d-a174-46fa-bb5a-97d05702bfcd
-- title:
--   Inequality (1), Step ii of the proof of Theorem 1 — approximate dual feasibility
-- statement:
--   Let $K\ge 1$, let $(x,y)$ be a run, and let $(\hat\alpha,\hat\beta)$ be an optimal dual of the last-stage LP. For each stage $k\in[K]$ and each edge $(i,j)\in E_k$,
--   $$
--   \alpha_i+\sum_{s=1}^k\Delta\beta_{s,j}\ge w_j\bigl(1-(1-1/K)^K\bigr).
--   $$
--   Since each $\Delta\beta_{s,j}$ is nonnegative, this gives the second requirement of the primal-dual certificate: $\alpha_i+\beta_j\ge\Gamma(K)w_j$ on every edge.
--
--   Differences from the source:
--   - generalization: capacities n_j = 1 "without the loss of generality" (p.12), and Algorithm 1 printed only for n_j = 1 → every real n_j > 0, with normalized levels y_j + Σ_i x_ij / n_j and the coefficient n_j in the regularizer and in the dual objective; reason: at n_j = 1 this is the printed text character for character, so the statement specializes to the source
--   - generalization: |U_k| ≥ 1 (p.12) → a batch may be empty, and U, V may be empty; reason: instances with nonempty batches are a subclass, and nothing in the proof uses nonemptiness
--   - reading: no cardinality assumption on U and V is printed → U and V are finite (Fintype); reason: the program and the LP are finite sums on the page, and footnote 8 and "no further assumptions" concern batch sizes
--   - encoding: the proof's y*_{k,j} = Σ_{s<k} Σ_i x*_{s,ij} → y^(k−1)_j, the level vector of the run; reason: an index shift; same numbers at n_j = 1
--   - reading: "the optimal dual solution" of the last-stage LP → every optimal dual; reason: the dual optimum need not be unique; every optimum is the strongest reading
--   - reading: α_i ← c^(l), with c^(l) undefined on a component with no offline vertex, and pairs of equal c merged (p.21) → α_i = pairPrice = 0 on such a component, and the components are not merged; reason: the corrected Proposition 2 sets c = 0 there, and the page’s merge puts such a vertex in l = 0, where c = 0, which is the same value; merging pairs of equal c changes no α_i and no Δβ_{k,j}
--   - reading: K ∈ ℕ → K ≥ 1; reason: the paper’s K > 0 (p.4); at K = 0 there are no stages and Γ(0) would be a division by zero
-- source:
--   Feng & Niazadeh, Batching and Optimal Multi-stage Bipartite Allocations, arXiv:2211.16581v1, proof of Theorem 1, [Step ii], inequality (1), pp.22–23

import Mathlib
import Definitions.Def_MultiStageAlloc_Run
import Definitions.Def_MultiStageAlloc_DualAssignment

namespace MultiStageAlloc

/-- **Inequality (1), Step ii of the proof of Theorem 1.** Feng & Niazadeh, arXiv:2211.16581v1,
pp.22–23. For every optimal dual of the last-stage LP, every stage `k ∈ [K]`, including `K`, and every
edge `(i, j) ∈ E_k`: `α_i + ∑_{s=1}^k Δβ_s,j ≥ w_j (1 - (1 - 1/K)^K)`. -/
theorem inequality_1 {U V : Type*} [Fintype U] [Fintype V] {K : ℕ} (hK : 1 ≤ K)
    (I : Instance U V K) (x : ℕ → U → V → ℝ) (y : ℕ → V → ℝ) (hrun : IsRun I x y)
    (a : U → ℝ) (b : V → ℝ) (hab : IsLastStageOptimalDual I (y (K - 1)) a b)
    (k : ℕ) (hk1 : 1 ≤ k) (hkK : k ≤ K) (i : U) (j : V) (hij : I.edge i j) (hik : I.batch i = k) :
    I.w j * (1 - (1 - 1 / (K : ℝ)) ^ K) ≤
      dualAlpha I x y a i + ∑ s ∈ Finset.Icc 1 k, deltaBeta I x y b s j := by sorry

end MultiStageAlloc
