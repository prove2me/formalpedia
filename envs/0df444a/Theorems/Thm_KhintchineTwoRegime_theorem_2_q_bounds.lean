-- Prove2me | Theorems.Thm_KhintchineTwoRegime_theorem_2_q_bounds
-- name    : KhintchineTwoRegime.theorem_2_q_bounds
-- status  : Proved
-- author  : @Mr Robbins
-- created : 2026-11-23T03:37:15.46186+00:00
-- url     : https://prove2.me/theorems/2a877d90-60cc-4e46-910a-d851a4d864a6
-- title:
--   Parameter bounds in the six-coordinate interval
-- statement:
--   If $\tau$ lies in the interval $[d_0,d_1]$ of Theorem 2 and $q=(2-\tau^2)/\sqrt2$, then
--   $$
--   \tau\ge0,\qquad \frac{\sqrt{483}}{22}\le q\le1.
--   $$
--   The lower endpoint $\tau=d_0$ corresponds to $q=1$, while the upper endpoint $\tau=d_1$ corresponds to $q=\sqrt{483}/22$.
--
--   These inequalities convert the geometric distance interval into the coefficient range used in Lemmas 5 and 6.
-- source:
--   Fang–Wang, A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions, arXiv:2608.27908v2, proof of Theorem 2, p.8 (the range sqrt(483)/22 <= q < 1 and q = (2-tau^2)/sqrt(2)).

import Mathlib

theorem KhintchineTwoRegime.theorem_2_q_bounds (τ : ℝ)
    (hτ : τ ∈ Set.Icc (Real.sqrt (2 - Real.sqrt 2)) (Real.sqrt (2 - Real.sqrt 966 / 22))) :
    0 ≤ τ ∧ Real.sqrt 483 / 22 ≤ (2 - τ ^ 2) / Real.sqrt 2 ∧
      (2 - τ ^ 2) / Real.sqrt 2 ≤ 1 := by sorry
