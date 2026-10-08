-- Prove2me | Theorems.Thm_NestedLogitVariants_PowersDelta_rpow_lower_bound_level
-- name    : NestedLogitVariants.PowersDelta.rpow_lower_bound_level
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T21:21:59.8195+00:00
-- url     : https://prove2.me/theorems/17a9207d-c6f8-4d98-9fe8-a89121284c79
-- title:
--   A.6, p. 54 — if δ^(l−1) ≤ a ≤ δ^l then (δ^l)^(γ−1) ≥ δ^(−[1−γ]^+) a^(γ−1)
-- statement:
--   Let $\delta > 1$, $\gamma > 0$, $l \in \mathbb Z$ and $a$ a real number with $\delta^{l-1} \le a \le \delta^l$. Then
--   $$(\delta^l)^{\gamma - 1} \ge \delta^{-[1 - \gamma]^+}\, a^{\gamma - 1},$$
--   where $[t]^+ = \max\{t, 0\}$.
--
--   In the proof of Theorem 12 this is applied with $a = V_i(S_i)$ for the arbitrary assortment $S_i$, to pass from display (36) back to $V_i(S_i)$.
--
--   **Formalization Note** $\delta^l$ and $\delta^{l-1}$ are integer powers; the outer powers are real powers. $\gamma > 0$ is the pinned standing assumption $\gamma_i > 0$.
-- source:
--   Davis, Gallego, Topaloglu, Assortment optimization under variants of the nested logit model, revised manuscript of June 18, 2013 (published Oper. Res. 62(2), 2014, DOI 10.1287/opre.2014.1256), p. 54, Appendix A.6, the bound on (δ^l)^{γ_i−1}

import Mathlib

namespace NestedLogitVariants.PowersDelta

/-- A.6, p. 54: if `δ^{l−1} ≤ a ≤ δ^l` (with `a = V_i(S_i)`), then
`(δ^l)^{γ−1} ≥ δ^{−[1−γ]^+} a^{γ−1}`, where `[t]^+ = max{t, 0}`. -/
theorem rpow_lower_bound_level (δ γ a : ℝ) (l : ℤ) (hδ : 1 < δ) (hγ : 0 < γ)
    (ha1 : δ ^ (l - 1) ≤ a) (ha2 : a ≤ δ ^ l) :
    δ ^ (-max (1 - γ) 0) * a ^ (γ - 1) ≤ (δ ^ l) ^ (γ - 1) := by sorry

end NestedLogitVariants.PowersDelta
