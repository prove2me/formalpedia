-- Prove2me | Theorems.Thm_OnlineUBSR_eq_29
-- name    : OnlineUBSR.eq_29
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:18:14.827987+00:00
-- url     : https://prove2.me/theorems/fc5c1df8-6c3b-4cc4-9dba-73c806c04248
-- title:
--   (29), p.18 — $(1+aJ)^2\le1-2a\mu_1+a^2L_1^2\le e^{-2\mu_1a+L_1^2a^2}$
-- statement:
--   Let $a>0$, $\mu_1>0$, and let $L_1$ and $J$ be real numbers with $-L_1\le J\le-\mu_1$. Then
--
--   $$
--   (1+aJ)^2\le1-2a\mu_1+a^2L_1^2\le\exp\big(-2\mu_1a+L_1^2a^2\big).
--   $$
--
--   In the proof of Theorem 1 this is applied with $a=a_k$ and $J=J_{k-1}$, and turns the one-step inequality (28) into the exponential form (30).
--
--   **Formalization Note** Stated for an arbitrary real $J$ in $[-L_1,-\mu_1]$.
--
--   Differences from the source:
--   - generalization: J = J_{k−1} for k ∈ {1, …, n − 1}, where −L₁ ≤ J_k ≤ −µ₁ → any real J with −L₁ ≤ J ≤ −µ₁; reason: covers every J_k, including J₀, which (30) also needs
--   - encoding: a_k a step size; µ₁ from Assumption 3 → a > 0 and µ₁ > 0; reason: step sizes are positive and Assumption 3 has µ₁ > 0
-- source:
--   Hegde, Menon, Prashanth & Jagannathan, Online Estimation and Optimization of Utility-Based Shortfall Risk, arXiv:2111.08805v3, §7.1, eq. (29), p.18

import Mathlib

open MeasureTheory ProbabilityTheory Real

namespace OnlineUBSR

/-- **The scalar contraction bound (29), p.18.**
Hegde, Menon, Prashanth & Jagannathan, arXiv:2111.08805v3, §7.1, (29), p.18: "From Assumption 3, we know that −L1 ≤ Jk ≤ −µ1 for all
k ∈ {1, . . . , n − 1}. Using this fact, we have (1 + akJk−1)² = 1 + 2akJk−1 + a²kJ²k−1 ≤
1 − 2akµ1 + a²kL²1 ≤ exp(−2µ1ak + L²1a²k). (29)"

For real numbers `a > 0`, `μ₁ > 0`, `L₁` and `J` with `−L₁ ≤ J ≤ −μ₁`:
`(1 + aJ)² ≤ 1 − 2aμ₁ + a²L₁² ≤ exp(−2μ₁a + L₁²a²)`.

**Formalization Note.** Stated for an arbitrary real `J ∈ [−L₁, −μ₁]`, so it applies to every
`J_k`, including `J_0`, which (28)–(30) use although the page writes `k ∈ {1, …, n − 1}`. -/
theorem eq_29
    (a μ₁ L₁ J : ℝ) (ha : 0 < a) (hμ₁ : 0 < μ₁) (hJl : -L₁ ≤ J) (hJu : J ≤ -μ₁) :
    (1 + a * J) ^ 2 ≤ 1 - 2 * a * μ₁ + a ^ 2 * L₁ ^ 2 ∧
    1 - 2 * a * μ₁ + a ^ 2 * L₁ ^ 2 ≤ Real.exp (-2 * μ₁ * a + L₁ ^ 2 * a ^ 2) := by sorry

end OnlineUBSR
