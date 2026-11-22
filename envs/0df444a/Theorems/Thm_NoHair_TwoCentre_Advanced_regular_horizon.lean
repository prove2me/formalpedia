-- Prove2me | Theorems.Thm_NoHair_TwoCentre_Advanced_regular_horizon
-- name    : NoHair.TwoCentre.Advanced.regular_horizon
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-22T21:29:49.579877+00:00
-- url     : https://prove2.me/theorems/5112e9cb-e66c-4ba3-ba7a-01031f4af387
-- title:
--   Analytic extension across one two-centre horizon and inward crossing of timelike curves
-- statement:
--   Extend the equal-mass two-centre Majumdar–Papapetrou metric across its left future horizon in advanced coordinates. On the explicit collar $|r|<1/4$, $|c|\leq 1$, all six metric and gauge-potential coefficients are real analytic, the angular scale is strictly positive, and the radial metric block has determinant $-1$. For $r>0$ the radial coefficient and the potential agree with the coordinate transformation $v=t+f(r)$, $f'(r)=H_0^2/r^2$, after adding the closed form $(H_0/r)\,dr$ to the potential. At $r=0$ the radial block is $\left(\begin{smallmatrix}0&1\\1&c\end{smallmatrix}\right)$, and the angular metric is the unit sphere metric.
--
--   If the continuous radial coordinate of a curve satisfies the corresponding future timelike cone inequalities at every point where it meets the horizon, it cannot evolve from $r(0)\leq0$ to $r(1)>0$.
-- source:
--   J. B. Hartle and S. W. Hawking, Solutions of the Einstein-Maxwell equations with many black holes, Commun. Math. Phys. 26 (1972), 87–101, §II, equations (2.1)–(2.13), https://doi.org/10.1007/BF01645696.

import Definitions.Def_NoHair_TwoCentreAdvanced

open Set NoHair.TwoCentre.Advanced

theorem NoHair.TwoCentre.Advanced.regular_horizon :
    (∀ p : ℝ × ℝ, |p.1| < 1 / 4 → |p.2| ≤ 1 →
      0 < H p ∧
      (∀ f ∈ [gvv, gvr, grr, angularScale, potentialV, potentialR], AnalyticAt ℝ f p) ∧
      gvv p * grr p - gvr p ^ 2 = -1 ∧
      (0 < p.1 → grr p = (H p ^ 4 - H₀ p ^ 4) / (p.1 ^ 2 * H p ^ 2) ∧
        potentialR p = -(H₀ p ^ 2 / (p.1 * H p)) + H₀ p / p.1)) ∧
    (∀ c : ℝ, gvv (0, c) = 0 ∧ gvr (0, c) = 1 ∧ grr (0, c) = c ∧ angularScale (0, c) = 1) ∧
    (∀ r : ℝ → ℝ, Continuous r → r 0 ≤ 0 →
      (∀ t ∈ Icc (0 : ℝ) 1, r t = 0 → ∃ b v w a : ℝ, HasDerivAt r w t ∧ 0 ≤ a ∧
        2 * v * w + b * w ^ 2 + a < 0 ∧ -v + (1 - b) * w / 2 < 0) → r 1 ≤ 0) := by
  sorry
