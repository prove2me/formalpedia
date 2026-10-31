-- Prove2me | Theorems.Thm_MultiwaySoS_lemma_16
-- name    : MultiwaySoS.lemma_16
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:17:10.224366+00:00
-- url     : https://prove2.me/theorems/6c8dc007-eeb6-4a31-b8f2-aa7ee5fab4b9
-- title:
--   Lemma 16 — $\sqrt{8a_t}-\sqrt{8a_0}\le4t+2\log(1+2t)$ for $a_t=a_{t-1}+\sqrt{8a_{t-1}}+2$
-- statement:
--   Let $a_0\ge0$ and $a_t=a_{t-1}+\sqrt{8a_{t-1}}+2$ for $t\ge1$. Then for every $t\ge0$,
--   $$\sqrt{8a_t}-\sqrt{8a_0}\le4t+2\log(1+2t).$$
--   This growth bound controls the compensator $\Xi^t$ in the proof of Lemma 8.
--
--   Differences from the source: none.
-- source:
--   Gupta, Greedy Algorithm for Multiway Matching with Bounded Regret, arXiv:2112.04622v3, Lemma 16, p.44

import Mathlib

namespace MultiwaySoS

/-- Lemma 16 (arXiv:2112.04622v3, p.44). Let `a_0 ≥ 0` and `a_t = a_{t−1} + √(8a_{t−1}) + 2`. Then
`√(8a_t) − √(8a_0) ≤ 4t + 2 log(1 + 2t)` for every `t`. -/
theorem lemma_16 (a : ℕ → ℝ) (h0 : 0 ≤ a 0)
    (ha : ∀ t, a (t + 1) = a t + Real.sqrt (8 * a t) + 2) (t : ℕ) :
    Real.sqrt (8 * a t) - Real.sqrt (8 * a 0) ≤ 4 * t + 2 * Real.log (1 + 2 * t) := by sorry

end MultiwaySoS
