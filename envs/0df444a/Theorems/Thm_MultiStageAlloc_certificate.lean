-- Prove2me | Theorems.Thm_MultiStageAlloc_certificate
-- name    : MultiStageAlloc.certificate
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:32:39.665254+00:00
-- url     : https://prove2.me/theorems/bfcd0784-f42e-4e9a-b436-60f903e76ceb
-- title:
--   §3.3, p.20 — primal-dual certificate of $\Gamma(K)$-competitiveness
-- statement:
--   Let $K\ge 1$ and let $(x,y)$ be a run. Suppose $\alpha_i,\beta_j\ge 0$ satisfy
--   $$
--   \mathrm{ALG}=\sum_{i\in U}\alpha_i+\sum_{j\in V}n_j\beta_j
--   \quad\text{and}\quad
--   \alpha_i+\beta_j\ge\Gamma(K)\,w_j\ \text{ for every }(i,j)\in E .
--   $$
--   Then $\Gamma(K)\cdot\mathrm{OPT}\le\mathrm{ALG}$.
--
--   This is the weak-duality step that reduces Theorem 1 to constructing such a dual assignment.
--
--   Differences from the source:
--   - generalization: capacities n_j = 1 "without the loss of generality" (p.12), and Algorithm 1 printed only for n_j = 1 → every real n_j > 0, with normalized levels y_j + Σ_i x_ij / n_j and the coefficient n_j in the regularizer and in the dual objective; reason: at n_j = 1 this is the printed text character for character, so the statement specializes to the source
--   - generalization: |U_k| ≥ 1 (p.12) → a batch may be empty, and U, V may be empty; reason: instances with nonempty batches are a subclass, and nothing in the proof uses nonemptiness
--   - reading: no cardinality assumption on U and V is printed → U and V are finite (Fintype); reason: the program and the LP are finite sums on the page, and footnote 8 and "no further assumptions" concern batch sizes
--   - reading: "primal is Γ(K)-competitive", i.e. ALG/OPT ≥ Γ(K) (Definition 1) → Γ(K) · OPT ≤ ALG; reason: Definition 1 is 0/0 on OPT = 0; the multiplicative form equals it on OPT > 0 and holds trivially otherwise
--   - encoding: x_k ∈ ℝ^{E_k} → x : U → V → ℝ vanishing off E_k; reason: sums over U and V are then the printed sums over E_k; same instances
--   - reading: K ∈ ℕ → K ≥ 1; reason: the paper’s K > 0 (p.4); at K = 0 there are no stages and Γ(0) would be a division by zero
-- source:
--   Feng & Niazadeh, Batching and Optimal Multi-stage Bipartite Allocations, arXiv:2211.16581v1, §3.3, p.20, "Existence of such a dual assignment will guarantee that primal is Γ(K)-competitive"

import Mathlib
import Definitions.Def_MultiStageAlloc_OfflineLP
import Definitions.Def_MultiStageAlloc_Run

namespace MultiStageAlloc

/-- **The primal-dual certificate.** Feng & Niazadeh, arXiv:2211.16581v1, §3.3, p.20: if a dual
assignment `α, β ≥ 0` has the objective of the run, `∑ α_i + ∑ n_j β_j = ALG`, and is approximately
feasible, `α_i + β_j ≥ Γ(K) w_j` on every edge, then "primal is `Γ(K)`-competitive". At `n_j = 1` the
dual objective is the printed `∑ α_i + ∑ β_j`. -/
theorem certificate {U V : Type*} [Fintype U] [Fintype V] {K : ℕ} (hK : 1 ≤ K) (I : Instance U V K)
    (x : ℕ → U → V → ℝ) (y : ℕ → V → ℝ) (hrun : IsRun I x y) (α : U → ℝ) (β : V → ℝ)
    (hα : ∀ i, 0 ≤ α i) (hβ : ∀ j, 0 ≤ β j)
    (hobj : ALG I x = ∑ i, α i + ∑ j, I.cap j * β j)
    (hfeas : ∀ i j, I.edge i j → gammaK K * I.w j ≤ α i + β j) :
    gammaK K * OPT I ≤ ALG I x := by sorry

end MultiStageAlloc
