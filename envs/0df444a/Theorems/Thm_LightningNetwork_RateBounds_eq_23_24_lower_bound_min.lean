-- Prove2me | Theorems.Thm_LightningNetwork_RateBounds_eq_23_24_lower_bound_min
-- name    : LightningNetwork.RateBounds.eq_23_24_lower_bound_min
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:55:02.649012+00:00
-- url     : https://prove2.me/theorems/27ca4fff-2700-4151-91ce-59bd32abb45d
-- title:
--   Eqs. (23)–(24): (23) bounds (21) from below and is minimized at $\hat m = (2B/\kappa^2)^{1/3}$ with value (24)
-- statement:
--   Let $B > 0$, $C > 0$, $\kappa > 0$, let $H(m) = 2m + B\bigl(2/(\kappa^2m^2) - 1/6\bigr) - 2C/\kappa^2$ and $\hat m = (2B/\kappa^2)^{1/3}$. Then
--
--   1. for every $m > 0$, $H(m) < 2m + \dfrac B2\operatorname{csch}^2\!\left(\dfrac{\kappa m}2\right) - \dfrac C2\operatorname{csch}^2\!\left(\dfrac\kappa2\right)$, the right side being (21) in hyperbolic form;
--   2. $H(\hat m) \le H(m)$ for every $m > 0$;
--   3. the minimum is
--   $$
--   H(\hat m) = 3\left(\frac{2B}{\kappa^2}\right)^{1/3} - \frac B6 - \frac{2C}{\kappa^2}. \tag{24}
--   $$
--
--   Differences from the source:
--   - reading: (21) is bounded from below by (23) → (23) < (21) strictly, for every m > 0; reason: the bound comes from the strict inequalities (22) with B > 0; the strict reading is the stronger one
--   - encoding: κ = log(1 + r/λ) with λ, r > 0 → κ is a real parameter, positive or bounded below by a positive quantity; reason: r/λ ↦ log(1 + r/λ) is a bijection of (0, ∞) onto (0, ∞), so the instances are the same
--   - encoding: csch² x → 1 / sinh x ^ 2; reason: Mathlib has no csch; the arguments are positive, so sinh x ≠ 0 and the values agree
-- source:
--   Guasoni, Huberman, Shikhelman, Lightning Network Economics: Channels, Management Science (2023), doi:10.1287/mnsc.2022.01664, proof of Theorem 2(ii), eqs. (23)–(24), pp. 11–12

import Mathlib
import Definitions.Def_LightningNetwork_RateBounds_cschLowerBound

namespace LightningNetwork.RateBounds

/-- **The lower bound (23) and its minimum (24).**
Guasoni, Huberman, Shikhelman, *Lightning Network Economics: Channels*, Management Science (2023),
doi:10.1287/mnsc.2022.01664, proof of Theorem 2(ii), eqs. (23)–(24), pp. 11–12: "whereby (21) is bounded from
below by 2m + B(2/(κ²m²) − 1/6) − 2C/κ². For m̂ = (2B/κ²)^{1/3}, this function reaches its
minimum, which is 3(2B/κ²)^{1/3} − B/6 − 2C/κ²."

For `B > 0`, `C > 0`, `κ > 0`, with `H(m) = 2m + B(2/(κ²m²) − 1/6) − 2C/κ²` and
`m̂ = (2B/κ²)^{1/3}`:
1. `H(m) < 2m + (B/2) csch²(κm/2) − (C/2) csch²(κ/2)` for every `m > 0`;
2. `H(m̂) ≤ H(m)` for every `m > 0`;
3. `H(m̂) = 3(2B/κ²)^{1/3} − B/6 − 2C/κ²`.

**Formalization Note.** The bound in clause 1 is strict, as (22) is. `csch² x` is
`1 / sinh x ^ 2`; the cube root is `Real.rpow` with exponent `1/3` of a positive number. -/
theorem eq_23_24_lower_bound_min (B C κ : ℝ) (hB : 0 < B) (hC : 0 < C) (hκ : 0 < κ) :
    (∀ m : ℝ, 0 < m →
        cschLowerBound κ B C m
          < 2 * m + B / 2 * (1 / Real.sinh (κ * m / 2) ^ 2)
            - C / 2 * (1 / Real.sinh (κ / 2) ^ 2)) ∧
      (∀ m : ℝ, 0 < m →
        cschLowerBound κ B C ((2 * B / κ ^ 2) ^ (1 / 3 : ℝ)) ≤ cschLowerBound κ B C m) ∧
      cschLowerBound κ B C ((2 * B / κ ^ 2) ^ (1 / 3 : ℝ))
        = 3 * (2 * B / κ ^ 2) ^ (1 / 3 : ℝ) - B / 6 - 2 * C / κ ^ 2 := by sorry

end LightningNetwork.RateBounds
