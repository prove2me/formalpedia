-- Prove2me | Theorems.Thm_MultiStageAlloc_run_feasible
-- name    : MultiStageAlloc.run_feasible
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:32:33.879339+00:00
-- url     : https://prove2.me/theorems/3064cdf2-2f8e-4cfa-9bf2-7d17810291c2
-- title:
--   §3.3, p.20 — a run of Algorithm 1 is a feasible primal assignment
-- statement:
--   Let $(x,y)$ be a run of PR-MWM. The sum of the stage allocations $z_{ij}=\sum_{k=1}^K x_{k,ij}$ is feasible for the offline primal LP, its objective value is $\mathrm{ALG}$, and each level vector $y^{(k)}$, $k\le K$, lies in $[0,1]^V$.
--
--   This is the "feasible primal assignment" of the primal-dual argument: it shows that the algorithm's output competes in the offline LP and keeps every later stage program well posed.
--
--   Differences from the source:
--   - generalization: capacities n_j = 1 "without the loss of generality" (p.12), and Algorithm 1 printed only for n_j = 1 → every real n_j > 0, with normalized levels y_j + Σ_i x_ij / n_j and the coefficient n_j in the regularizer and in the dual objective; reason: at n_j = 1 this is the printed text character for character, so the statement specializes to the source
--   - generalization: |U_k| ≥ 1 (p.12) → a batch may be empty, and U, V may be empty; reason: instances with nonempty batches are a subclass, and nothing in the proof uses nonemptiness
--   - reading: no cardinality assumption on U and V is printed → U and V are finite (Fintype); reason: the program and the LP are finite sums on the page, and footnote 8 and "no further assumptions" concern batch sizes
--   - encoding: x_k ∈ ℝ^{E_k} → x : U → V → ℝ vanishing off E_k; reason: sums over U and V are then the printed sums over E_k; same instances
--   - reading: feasibility is asserted in passing ("the feasible primal assignment") → a statement with the value identity and the range of the levels; reason: these are what the certificate and later stages use
-- source:
--   Feng & Niazadeh, Batching and Optimal Multi-stage Bipartite Allocations, arXiv:2211.16581v1, §3.3, p.20, "the feasible primal assignment"

import Mathlib
import Definitions.Def_MultiStageAlloc_OfflineLP
import Definitions.Def_MultiStageAlloc_Run

namespace MultiStageAlloc

/-- **A run is a feasible primal assignment.** Feng & Niazadeh, arXiv:2211.16581v1, §3.3, p.20: "the
feasible primal assignment `{x*_k}_{k∈[K]}` produced by Algorithm 1". The sum of the stage allocations
is feasible for the offline LP with value `ALG`, and the levels `y^(k)`, `k ≤ K`, stay in `[0, 1]`. -/
theorem run_feasible {U V : Type*} [Fintype U] [Fintype V] {K : ℕ} (I : Instance U V K)
    (x : ℕ → U → V → ℝ) (y : ℕ → V → ℝ) (hrun : IsRun I x y) :
    OfflineFeasible I (fun i j => ∑ k ∈ Finset.Icc 1 K, x k i j) ∧
    offlineValue I (fun i j => ∑ k ∈ Finset.Icc 1 K, x k i j) = ALG I x ∧
    ∀ k, k ≤ K → ∀ j, y k j ∈ Set.Icc (0 : ℝ) 1 := by sorry

end MultiStageAlloc
