-- Prove2me | Theorems.Thm_OLPRegret_theorem_1
-- name    : OLPRegret.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:04:55.706242+00:00
-- url     : https://prove2.me/theorems/881af072-690d-434e-8a9f-4350a74d93f1
-- title:
--   Theorem 1 — the optimal online policy has regret $O(\log n)$
-- statement:
--   Under Assumptions 2–6, there are $C>0$ and $N$ such that for all $n\ge N$,
--   $$
--   \mathrm E(V_n^\beta)-\mathrm E(v_n^\beta)\le C\log n,
--   $$
--   where $\mathrm E(v_n^\beta)=W_n(\beta)$ is the optimal policy's value. The lower-bound argument uses this upper bound.
--
--   Differences from the source:
--   - encoding: $\mathrm E(R_n)=O(\log n)$ for the optimal policy → $\mathrm E(V_n^\beta)-W_n(\beta)\le C\log n$ for $n\ge N$; reason: $W_n(\beta)=\mathrm E(v_n^\beta)$ by `OLPRegret.bellman_optimal`; `Real.log` is the natural logarithm, and the base only rescales $C$
-- source:
--   Bray, arXiv:1912.08917v6, Theorem 1, p.21

import Mathlib
import Definitions.Def_OLPRegret_regret
import Definitions.Def_OLPRegret_bellmanValue

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal Topology

namespace OLPRegret

/-- Bray, arXiv:1912.08917v6, Theorem 1, p.21: the optimal policy of the online linear program without
learning has `E(Rₙ) = O(log n)` as `n → ∞` when `μ` is known. Here `E(Rₙ) = E(Vₙᵝ) − E(vₙᵝ)` and
`E(vₙᵝ) = W n β` by `OLPRegret.bellman_optimal`. -/
theorem theorem_1 {m : ℕ} (μ : Measure (Customer m)) [IsProbabilityMeasure μ] (β : E m)
    (hβ : VNonneg β) (hA : Assumptions μ β) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n ≥ N,
      ∫ ω, offlineIP ω β ∂sampleLaw μ n - W μ n β ≤ C * Real.log n := by sorry

end OLPRegret
