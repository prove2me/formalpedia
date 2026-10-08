-- Prove2me | Theorems.Thm_NestedLogitVariants_PowersDelta_rpow_lower_bound_hat
-- name    : NestedLogitVariants.PowersDelta.rpow_lower_bound_hat
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T21:21:43.101704+00:00
-- url     : https://prove2.me/theorems/dde58483-8bf1-44e6-a3b1-cb79da31402a
-- title:
--   A.6, p. 53 — if δ^(l−1) ≤ a ≤ δ^l then a^(γ−1) ≥ (δ^l)^(γ−1) δ^(−[γ−1]^+)
-- statement:
--   Let $\delta > 1$, $\gamma > 0$, $l \in \mathbb Z$ and $a$ a real number with $\delta^{l-1} \le a \le \delta^l$. Then
--   $$a^{\gamma - 1} \ge (\delta^l)^{\gamma - 1}\, \delta^{-[\gamma - 1]^+},$$
--   where $[t]^+ = \max\{t, 0\}$.
--
--   In the proof of Theorem 12 this is applied with $a = V_i(\hat S_{il})$ and $\gamma = \gamma_i$, to bound the factor $V_i(\hat S_{il})^{\gamma_i - 1}$ in display (34) from below.
--
--   **Formalization Note** $\delta^l$ and $\delta^{l-1}$ are integer powers; the outer powers are real powers. $\gamma > 0$ is the pinned standing assumption $\gamma_i > 0$.
-- source:
--   Davis, Gallego, Topaloglu, Assortment optimization under variants of the nested logit model, revised manuscript of June 18, 2013 (published Oper. Res. 62(2), 2014, DOI 10.1287/opre.2014.1256), p. 53, Appendix A.6, the bound on V_i(Ŝ_il)^{γ_i−1}

import Mathlib

namespace NestedLogitVariants.PowersDelta

/-- A.6, p. 53: if `δ^{l−1} ≤ a ≤ δ^l` (with `a = V_i(Ŝ_il)`), then
`a^{γ−1} ≥ (δ^l)^{γ−1} δ^{−[γ−1]^+}`, where `[t]^+ = max{t, 0}`. -/
theorem rpow_lower_bound_hat (δ γ a : ℝ) (l : ℤ) (hδ : 1 < δ) (hγ : 0 < γ)
    (ha1 : δ ^ (l - 1) ≤ a) (ha2 : a ≤ δ ^ l) :
    (δ ^ l) ^ (γ - 1) * δ ^ (-max (γ - 1) 0) ≤ a ^ (γ - 1) := by sorry

end NestedLogitVariants.PowersDelta
