-- Prove2me | Theorems.Thm_LightningNetwork_RateBounds_eq_21_hyperbolic_form
-- name    : LightningNetwork.RateBounds.eq_21_hyperbolic_form
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:54:10.624074+00:00
-- url     : https://prove2.me/theorems/cf7a0e9f-e396-4abb-8a01-b1fe23e0d437
-- title:
--   Proof of Theorem 2(ii): with $\alpha = e^\kappa$, (21) equals $2m + \frac B2\operatorname{csch}^2(\kappa m/2) - \frac C2\operatorname{csch}^2(\kappa/2)$
-- statement:
--   Let $\kappa > 0$, $m > 0$ and $B, C \in \mathbb R$, and set $\alpha = e^\kappa$. Then
--
--   $$
--   2m + \frac{2B\alpha^m}{(\alpha^m-1)^2} - \frac{2C\alpha}{(\alpha-1)^2} \;=\; 2m + \frac B2 \operatorname{csch}^2\!\left(\frac{\kappa m}{2}\right) - \frac C2 \operatorname{csch}^2\!\left(\frac\kappa2\right).
--   $$
--
--   In the proof $\kappa = \log\alpha_+$ is the constant $\kappa$ of Theorem 2(ii).
--
--   Differences from the source:
--   - encoding: κ = log(1 + r/λ) with λ, r > 0 → κ is a real parameter, positive or bounded below by a positive quantity; reason: r/λ ↦ log(1 + r/λ) is a bijection of (0, ∞) onto (0, ∞), so the instances are the same
--   - encoding: csch² x → 1 / sinh x ^ 2; reason: Mathlib has no csch; the arguments are positive, so sinh x ≠ 0 and the values agree
--   - generalization: B > 0 (the cost of resetting a channel) → B any real number; reason: the identity is linear in B
--   - generalization: C > 0 (the cost of an on-chain transaction) → C any real number; reason: the identity is linear in C
-- source:
--   Guasoni, Huberman, Shikhelman, Lightning Network Economics: Channels, Management Science (2023), doi:10.1287/mnsc.2022.01664, proof of Theorem 2(ii), unnumbered display after eq. (21), p. 11

import Mathlib

namespace LightningNetwork.RateBounds

/-- **Proof of Theorem 2(ii), unnumbered display after (21): the hyperbolic form.**
Guasoni, Huberman, Shikhelman, *Lightning Network Economics: Channels*, Management Science (2023),
doi:10.1287/mnsc.2022.01664, proof of Theorem 2(ii), p. 11: "Setting α = e^κ, the function reduces to
2m + (B/2)csch²(κm/2) − (C/2)csch²(κ/2)."

For `κ > 0`, `m > 0` and any `B`, `C`, with `α = e^κ`:
`2m + 2Bα^m/(α^m − 1)² − 2Cα/(α − 1)² = 2m + (B/2) csch²(κm/2) − (C/2) csch²(κ/2)`.

**Formalization Note.** `csch² x` is written `1 / sinh x ^ 2` (Mathlib has no `csch`); its
arguments are positive here. `α^m` is `Real.rpow`. -/
theorem eq_21_hyperbolic_form (κ B C m : ℝ) (hκ : 0 < κ) (hm : 0 < m) :
    2 * m + 2 * B * Real.exp κ ^ m / (Real.exp κ ^ m - 1) ^ 2
        - 2 * C * Real.exp κ / (Real.exp κ - 1) ^ 2
      = 2 * m + B / 2 * (1 / Real.sinh (κ * m / 2) ^ 2)
        - C / 2 * (1 / Real.sinh (κ / 2) ^ 2) := by sorry

end LightningNetwork.RateBounds
