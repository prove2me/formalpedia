-- Prove2me | Theorems.Thm_LightningNetwork_RateBounds_eq_18_min_positive
-- name    : LightningNetwork.RateBounds.eq_18_min_positive
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:50:41.89074+00:00
-- url     : https://prove2.me/theorems/ebcc54c9-968e-4099-b6c7-21d5f48e8fd9
-- title:
--   Eq. (18): $F(\hat m) > 0$ for $\kappa \ge \frac1B\max\bigl(\frac{\alpha^2}{1-\alpha}, 2(\cosh(C-\alpha)-1)\bigr)$
-- statement:
--   Let $B > 0$, $C > 0$ and $0 < \alpha < 1$. If
--
--   $$
--   \kappa \;\ge\; \frac1B \max\left(\frac{\alpha^2}{1-\alpha},\; 2\bigl(\cosh(C-\alpha) - 1\bigr)\right),
--   $$
--
--   then, with $\hat m = \cosh^{-1}(B\kappa/2+1)/\kappa$ and $F(m) = C/(1-e^\kappa) + B/(e^{\kappa m}-1) + m$,
--
--   $$
--   F(\hat m) > 0 .
--   $$
--
--   So for such $\kappa$ no unidirectional channel is cheaper than on-chain settlement.
--
--   Differences from the source:
--   - encoding: κ = log(1 + r/λ) with λ, r > 0 → κ is a real parameter, positive or bounded below by a positive quantity; reason: r/λ ↦ log(1 + r/λ) is a bijection of (0, ∞) onto (0, ∞), so the instances are the same
-- source:
--   Guasoni, Huberman, Shikhelman, Lightning Network Economics: Channels, Management Science (2023), doi:10.1287/mnsc.2022.01664, proof of Theorem 2(i), eq. (18), p. 11

import Mathlib
import Definitions.Def_LightningNetwork_RateBounds_uniExcess

namespace LightningNetwork.RateBounds

/-- **Inequality (18).**
Guasoni, Huberman, Shikhelman, *Lightning Network Economics: Channels*, Management Science (2023),
doi:10.1287/mnsc.2022.01664, proof of Theorem 2(i), eq. (18), p. 11:
"F(m̂) > 0 for κ ≥ (1/B)max(α²/(1 − α), 2(cosh(C − α) − 1))."

For `B > 0`, `C > 0`, `0 < α < 1`, if `κ ≥ (1/B)·max(α²/(1 − α), 2(cosh(C − α) − 1))` then,
with `m̂ = arcosh(Bκ/2 + 1)/κ`, `F(m̂) > 0`.

**Formalization Note.** `κ > 0` follows from the hypotheses. -/
theorem eq_18_min_positive (B C α κ : ℝ) (hB : 0 < B) (hC : 0 < C) (hα0 : 0 < α)
    (hα1 : α < 1)
    (hκ : 1 / B * max (α ^ 2 / (1 - α)) (2 * (Real.cosh (C - α) - 1)) ≤ κ) :
    0 < uniExcess κ B C (Real.arcosh (B * κ / 2 + 1) / κ) := by sorry

end LightningNetwork.RateBounds
