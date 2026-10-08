-- Prove2me | Theorems.Thm_NestedLogitVariants_PowersDelta_exponent_ge_one
-- name    : NestedLogitVariants.PowersDelta.exponent_ge_one
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T21:21:57.266771+00:00
-- url     : https://prove2.me/theorems/e13d7ac9-00ef-418c-bc2e-d5f708039394
-- title:
--   A.6, p. 54 — δ^γ̄ δ^(−[γ_i−1]^+) δ^(−[1−γ_i]^+) ≥ 1 and δ^(γ̄+γ_i+1) ≤ δ^(2γ̄+1)
-- statement:
--   Let $\delta > 1$, $0 < \gamma \le \bar\gamma$ and $\bar\gamma > 1$. Then
--   $$\delta^{\bar\gamma}\, \delta^{-[\gamma - 1]^+}\, \delta^{-[1 - \gamma]^+} \ge 1 \qquad \text{and} \qquad \delta^{\bar\gamma + \gamma + 1} \le \delta^{2\bar\gamma + 1},$$
--   where $[t]^+ = \max\{t, 0\}$.
--
--   Applied with $\gamma = \gamma_i$ and $\bar\gamma = \max_i \gamma_i$, these two inequalities remove the extra powers of $\delta$ in the last step of the nonempty case of the proof of Theorem 12; the first is where the standing assumption $\bar\gamma > 1$ of §6 is used.
--
--   **Formalization Note** All powers are real powers.
-- source:
--   Davis, Gallego, Topaloglu, Assortment optimization under variants of the nested logit model, revised manuscript of June 18, 2013 (published Oper. Res. 62(2), 2014, DOI 10.1287/opre.2014.1256), p. 54, Appendix A.6, the exponent argument

import Mathlib

namespace NestedLogitVariants.PowersDelta

/-- A.6, p. 54: for `δ > 1`, `0 < γ ≤ γ̄` and `γ̄ > 1`,
`δ^{γ̄} δ^{−[γ−1]^+} δ^{−[1−γ]^+} ≥ 1` and `δ^{γ̄+γ+1} ≤ δ^{2γ̄+1}`. -/
theorem exponent_ge_one (δ γ γbar : ℝ) (hδ : 1 < δ) (hγ : 0 < γ) (hγle : γ ≤ γbar)
    (hγbar1 : 1 < γbar) :
    1 ≤ δ ^ γbar * δ ^ (-max (γ - 1) 0) * δ ^ (-max (1 - γ) 0) ∧
      δ ^ (γbar + γ + 1) ≤ δ ^ (2 * γbar + 1) := by sorry

end NestedLogitVariants.PowersDelta
