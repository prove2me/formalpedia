-- Prove2me | Theorems.Thm_NicaiseDelayWave_BoundaryInstab_eq5_5_5_7_delay_choice
-- name    : NicaiseDelayWave.BoundaryInstab.eq5_5_5_7_delay_choice
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T20:52:18.936548+00:00
-- url     : https://prove2.me/theorems/01e56cf0-a171-4c25-a695-a6dbb6fc6632
-- title:
--   (5.5)–(5.7) — the delays bτ = arccos(−μ1/μ2) + 2lπ make the boundary coefficient real: (μ1 + μ2e^{−ibτ})ib = b√(μ2² − μ1²)
-- statement:
--   Let $0 < \mu_1 \le \mu_2$, $b > 0$ and $l \in \mathbb N$, and put
--   $$\tau = \frac{\arccos(-\mu_1/\mu_2) + 2l\pi}{b}.$$
--   Then:
--
--   1. $\tau > 0$;
--   2. $\cos(b\tau) = -\mu_1/\mu_2$, which is (5.5);
--   3. $\mu_2 \sin(b\tau) = \sqrt{\mu_2^2 - \mu_1^2}$, which is (5.6);
--   4. the boundary coefficient of (5.4) is real:
--   $$(\mu_1 + \mu_2 e^{-ib\tau})\, ib = b\sqrt{\mu_2^2-\mu_1^2}.$$
--
--   Consequently, for $\lambda = ib$ the variational eigenvalue problem (5.4) becomes (5.7), with the real coefficient $b\sqrt{\mu_2^2-\mu_1^2}$ in front of the boundary integral, and the delays $\tau$ form, for fixed $b$, a strictly increasing sequence indexed by $l$ (the choice made on p. 1582).
--
--   **Formalization Note** $\arccos$ is Mathlib's real arccosine, with values in $[0,\pi]$; the hypothesis $\mu_1 \le \mu_2$ ensures $-\mu_1/\mu_2 \in [-1, 0)$.
-- source:
--   Nicaise, Pignotti, Stability and Instability Results of the Wave Equation with a Delay Term in the Boundary or Internal Feedbacks, SIAM J. Control Optim. 45 (2006), p. 1580, §5.1, (5.4)–(5.7), and p. 1582 (bτ = arccos(−μ1/μ2) + 2lπ)

import Mathlib

namespace NicaiseDelayWave.BoundaryInstab

/-- (5.5)–(5.7) and p. 1582: for `0 < μ₁ ≤ μ₂`, `b > 0`, `l ∈ ℕ`, the delay
`τ = (arccos(-μ₁/μ₂) + 2lπ)/b` is positive, satisfies `cos(bτ) = -μ₁/μ₂` (5.5) and
`μ₂ sin(bτ) = √(μ₂² - μ₁²)` (5.6), and turns the boundary coefficient of (5.4) into
`(μ₁ + μ₂ e^{-ibτ}) i b = b √(μ₂² - μ₁²)`, the coefficient of (5.7). -/
theorem eq5_5_5_7_delay_choice (μ1 μ2 b : ℝ) (hμ1 : 0 < μ1) (h18 : μ1 ≤ μ2) (hb : 0 < b)
    (l : ℕ) :
    let τ := (Real.arccos (-μ1 / μ2) + 2 * l * Real.pi) / b
    0 < τ ∧ Real.cos (b * τ) = -μ1 / μ2 ∧
      μ2 * Real.sin (b * τ) = Real.sqrt (μ2 ^ 2 - μ1 ^ 2) ∧
      ((μ1 : ℂ) + (μ2 : ℂ) * Complex.exp (-(Complex.I * b) * τ)) * (Complex.I * b) =
        ((b * Real.sqrt (μ2 ^ 2 - μ1 ^ 2) : ℝ) : ℂ) := by sorry

end NicaiseDelayWave.BoundaryInstab
