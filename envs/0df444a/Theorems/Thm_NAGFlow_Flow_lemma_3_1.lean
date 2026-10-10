-- Prove2me | Theorems.Thm_NAGFlow_Flow_lemma_3_1
-- name    : NAGFlow.Flow.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T15:34:30.926444+00:00
-- url     : https://prove2.me/theorems/d0900e24-0730-4295-bb90-70c8ba575710
-- title:
--   Lemma 3.1, p. 13 — 2(u − v, v − w) = ‖u − w‖² − ‖u − v‖² − ‖v − w‖²
-- statement:
--   Let $V$ be a real inner product space with inner product $(\cdot,\cdot)$ and induced norm $\|\cdot\|$. For any $u,v,w\in V$,
--   $$2(u-v,\,v-w)=\|u-w\|^2-\|u-v\|^2-\|v-w\|^2 .$$
--
--   This three-point identity is used in the paper both in the continuous analysis (to rewrite the term $\mu(x-v,v-x^*)$ in the derivative of the Lyapunov function) and in every discrete analysis.
-- source:
--   Luo & Chen, arXiv:1909.03145v4, Lemma 3.1, p. 13

import Mathlib

namespace NAGFlow.Flow

open scoped InnerProductSpace

/-- Lemma 3.1, p. 13. In a real inner product space, for any `u, v, w`,
`2(u − v, v − w) = ‖u − w‖² − ‖u − v‖² − ‖v − w‖²`. -/
theorem lemma_3_1 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (u v w : V) :
    2 * ⟪u - v, v - w⟫_ℝ = ‖u - w‖ ^ 2 - ‖u - v‖ ^ 2 - ‖v - w‖ ^ 2 := by sorry

end NAGFlow.Flow
