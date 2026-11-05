-- Prove2me | Theorems.Thm_MultiStageAlloc_theorem_1
-- name    : MultiStageAlloc.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:32:23.041521+00:00
-- url     : https://prove2.me/theorems/5774c17e-55b5-4c25-be4c-af667c1eb5e2
-- title:
--   Theorem 1 — PR-MWM is $\Gamma(K)$-competitive for $K$-stage fractional vertex weighted matching
-- statement:
--   In the $K$-stage fractional vertex weighted matching problem, the algorithm PR-MWM (Algorithm 1) is $\Gamma(K)$-competitive against the offline optimum, where
--   $$
--   \Gamma(K)=1-\Bigl(1-\frac1K\Bigr)^K .
--   $$
--   Precisely, for every $K\ge 1$ and every finite instance, a run of Algorithm 1 exists, and every run satisfies
--   $$
--   \Gamma(K)\cdot\mathrm{OPT}(I)\le\mathrm{ALG}(I).
--   $$
--   The ratio decreases from $\Gamma(1)=1$ through $\Gamma(2)=3/4$ to $1-1/e$, so batching beats the optimal online ratio. This is the central result of the source.
--
--   **Formalization Note** $\mathrm{OPT}$ is the optimal value of the fractional offline LP.
--
--   Differences from the source:
--   - generalization: capacities n_j = 1 "without the loss of generality" (p.12), and Algorithm 1 printed only for n_j = 1 → every real n_j > 0, with normalized levels y_j + Σ_i x_ij / n_j and the coefficient n_j in the regularizer and in the dual objective; reason: at n_j = 1 this is the printed text character for character, so the statement specializes to the source
--   - generalization: |U_k| ≥ 1 (p.12) → a batch may be empty, and U, V may be empty; reason: instances with nonempty batches are a subclass, and nothing in the proof uses nonemptiness
--   - reading: no cardinality assumption on U and V is printed → U and V are finite (Fintype); reason: the program and the LP are finite sums on the page, and footnote 8 and "no further assumptions" concern batch sizes
--   - encoding: x_k ∈ ℝ^{E_k} → x : U → V → ℝ vanishing off E_k; reason: sums over U and V are then the printed sums over E_k; same instances
--   - reading: "its unique optimal solution" (p.17), which makes PR-MWM a function → every choice of an optimal solution at every stage, and a run exists; reason: uniqueness is false in general (two online vertices sharing one offline vertex); every run is the strongest reading, covers the adaptive adversary of footnote 10, and existence keeps the clause from being vacuous
--   - reading: inf ALG(I)/OPT(I) ≥ α (Definition 1) → Γ(K) · OPT(I) ≤ ALG(I) for every instance; reason: the ratio is 0/0 on OPT = 0; the multiplicative form equals the printed one on OPT > 0 and holds trivially otherwise
--   - reading: OPT(I), "the optimum offline solution" → the optimal value of the fractional offline LP; reason: the LP of p.20, the strongest of the two possible benchmarks
--   - reading: K ∈ ℕ → K ≥ 1; reason: the paper’s K > 0 (p.4); Γ(0) would be a division by zero
-- source:
--   Feng & Niazadeh, Batching and Optimal Multi-stage Bipartite Allocations, arXiv:2211.16581v1, Theorem 1, p.18

import Mathlib
import Definitions.Def_MultiStageAlloc_OfflineLP
import Definitions.Def_MultiStageAlloc_Run

namespace MultiStageAlloc

/-- **Theorem 1 (Optimal Multi-Stage Algorithm for Weighted Bipartite Matching).** Feng & Niazadeh,
*Batching and Optimal Multi-stage Bipartite Allocations*, arXiv:2211.16581v1, p.18. In the `K`-stage
(fractional) vertex weighted matching problem, PR-MWM (Algorithm 1) is `Γ(K)`-competitive, where
`Γ(K) = 1 - (1 - 1/K)^K`: for every `K ≥ 1` and every instance, a run of Algorithm 1 exists, and every
run has `Γ(K) · OPT(I) ≤ ALG(I)`.

**Formalization Note.** Definition 1's `inf ALG(I)/OPT(I) ≥ α` (p.14) is `0/0` when `OPT(I) = 0`; the
multiplicative form equals it on `OPT(I) > 0` and holds trivially otherwise. `OPT` is the fractional
offline LP value, and capacities are real (the printed model is `cap = 1`). -/
theorem theorem_1 {U V : Type*} [Fintype U] [Fintype V] (K : ℕ) (hK : 1 ≤ K)
    (I : Instance U V K) :
    (∃ x y, IsRun I x y) ∧ ∀ x y, IsRun I x y → gammaK K * OPT I ≤ ALG I x := by sorry

end MultiStageAlloc
