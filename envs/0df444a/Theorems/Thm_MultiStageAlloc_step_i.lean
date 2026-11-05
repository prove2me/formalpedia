-- Prove2me | Theorems.Thm_MultiStageAlloc_step_i
-- name    : MultiStageAlloc.step_i
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:33:43.832862+00:00
-- url     : https://prove2.me/theorems/2829e198-8c2f-46f2-94a4-24a5c1aeb287
-- title:
--   Proof of Theorem 1, Step i, p.22 — primal and dual objectives agree
-- statement:
--   Let $K\ge 1$ and let $(x,y)$ be a run. An optimal dual solution $(\hat\alpha,\hat\beta)$ of the last-stage LP exists, and for each such solution the dual assignment of the proof of Theorem 1 has the objective of the run:
--   $$
--   \sum_{k=1}^K\sum_{(i,j)\in E_k}w_jx_{k,ij}=\sum_{i\in U}\alpha_i+\sum_{j\in V}n_j\beta_j .
--   $$
--   This is the first of the two requirements of the primal-dual certificate.
--
--   Differences from the source:
--   - generalization: capacities n_j = 1 "without the loss of generality" (p.12), and Algorithm 1 printed only for n_j = 1 → every real n_j > 0, with normalized levels y_j + Σ_i x_ij / n_j and the coefficient n_j in the regularizer and in the dual objective; reason: at n_j = 1 this is the printed text character for character, so the statement specializes to the source
--   - generalization: |U_k| ≥ 1 (p.12) → a batch may be empty, and U, V may be empty; reason: instances with nonempty batches are a subclass, and nothing in the proof uses nonemptiness
--   - reading: no cardinality assumption on U and V is printed → U and V are finite (Fintype); reason: the program and the LP are finite sums on the page, and footnote 8 and "no further assumptions" concern batch sizes
--   - encoding: x_k ∈ ℝ^{E_k} → x : U → V → ℝ vanishing off E_k; reason: sums over U and V are then the printed sums over E_k; same instances
--   - encoding: the proof's y*_{k,j} = Σ_{s<k} Σ_i x*_{s,ij} → y^(k−1)_j, the level vector of the run; reason: an index shift; same numbers at n_j = 1
--   - reading: "the optimal dual solution" of the last-stage LP → an optimal dual exists, and the identity holds for every optimal dual; reason: the dual optimum need not be unique; every optimum is the strongest reading, and existence keeps the clause from being vacuous
--   - reading: the identity compared pair by pair, using "x*_{k,ij} > 0 only if i and j belong to the same pair" → the global identity over all stages; reason: the printed "only if" fails when i ∈ U^(0) also sends mass to a zero-weight vertex that is not full; the global identity is the claim the certificate needs and it still holds
--   - reading: α_i ← c^(l), with c^(l) undefined on a component with no offline vertex, and pairs of equal c merged (p.21) → α_i = pairPrice = 0 on such a component, and the components are not merged; reason: the corrected Proposition 2 sets c = 0 there, and the page’s merge puts such a vertex in l = 0, where c = 0, which is the same value; merging pairs of equal c changes no α_i and no Δβ_{k,j}
--   - reading: K ∈ ℕ → K ≥ 1; reason: the paper’s K > 0 (p.4); at K = 0 there are no stages and Γ(0) would be a division by zero
-- source:
--   Feng & Niazadeh, Batching and Optimal Multi-stage Bipartite Allocations, arXiv:2211.16581v1, proof of Theorem 1, [Step i], p.22

import Mathlib
import Definitions.Def_MultiStageAlloc_Run
import Definitions.Def_MultiStageAlloc_DualAssignment

namespace MultiStageAlloc

/-- **Step i of the proof of Theorem 1: primal and dual objectives agree.** Feng & Niazadeh,
arXiv:2211.16581v1, p.22. An optimal dual of the last-stage LP exists, and for every one of them the
dual assignment built from the decomposition of Proposition 2 has
`∑ α_i + ∑ n_j β_j = ALG`.

**Formalization Note.** Stated globally rather than pair by pair, because the page's "`x*_{k,ij} > 0`
only if `i` and `j` belong to the same pair" fails when `i ∈ U^(0)_k` also sends mass to a zero-weight
vertex that is not full. -/
theorem step_i {U V : Type*} [Fintype U] [Fintype V] {K : ℕ} (hK : 1 ≤ K) (I : Instance U V K)
    (x : ℕ → U → V → ℝ) (y : ℕ → V → ℝ) (hrun : IsRun I x y) :
    (∃ a b, IsLastStageOptimalDual I (y (K - 1)) a b) ∧
    ∀ a b, IsLastStageOptimalDual I (y (K - 1)) a b →
      ALG I x = ∑ i, dualAlpha I x y a i + ∑ j, I.cap j * dualBeta I x y b j := by sorry

end MultiStageAlloc
