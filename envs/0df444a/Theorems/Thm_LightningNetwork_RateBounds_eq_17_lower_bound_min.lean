-- Prove2me | Theorems.Thm_LightningNetwork_RateBounds_eq_17_lower_bound_min
-- name    : LightningNetwork.RateBounds.eq_17_lower_bound_min
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:50:05.547762+00:00
-- url     : https://prove2.me/theorems/67c989f7-4956-49d0-adca-ed332cb74618
-- title:
--   Eq. (17): lower bound for the minimum $F(\hat m)$
-- statement:
--   Let $B > 0$ (reset cost), $C > 0$ (on-chain cost) and $0 < \alpha < 1$, and let $F(m) = C/(1-e^\kappa) + B/(e^{\kappa m}-1) + m$. If $\kappa \ge \alpha^2/(B(1-\alpha))$, then with $\hat m = \cosh^{-1}(B\kappa/2+1)/\kappa$,
--
--   $$
--   F(\hat m) \;>\; -\frac C\kappa + \frac\alpha\kappa + \frac{\cosh^{-1}\!\left(\frac{B\kappa}{2}+1\right)}{\kappa}.
--   $$
--
--   It follows from the minimum value of $F$, the estimate $C/(1-e^\kappa) > -C/\kappa$ and (16).
--
--   Differences from the source:
--   - encoding: κ = log(1 + r/λ) with λ, r > 0 → κ is a real parameter, positive or bounded below by a positive quantity; reason: r/λ ↦ log(1 + r/λ) is a bijection of (0, ∞) onto (0, ∞), so the instances are the same
-- source:
--   Guasoni, Huberman, Shikhelman, Lightning Network Economics: Channels, Management Science (2023), doi:10.1287/mnsc.2022.01664, proof of Theorem 2(i), eq. (17), p. 11

import Mathlib
import Definitions.Def_LightningNetwork_RateBounds_uniExcess

namespace LightningNetwork.RateBounds

/-- **Inequality (17).**
Guasoni, Huberman, Shikhelman, *Lightning Network Economics: Channels*, Management Science (2023),
doi:10.1287/mnsc.2022.01664, proof of Theorem 2(i), eq. (17), p. 11: "note first that the elementary
estimate e^x > 1 + x for x > 0 implies that C/(1 − e^κ) > −C/κ for all κ > 0. Note also that (16)
… whence the lower bound F(m̂) > −C/κ + α/κ + cosh⁻¹(Bκ/2 + 1)/κ for κ ≥ α²/(B(1 − α))."

For a reset cost `B > 0`, an on-chain cost `C > 0` and `0 < α < 1`, if `κ ≥ α²/(B(1 − α))`
then, with `m̂ = arcosh(Bκ/2 + 1)/κ` and `F = uniExcess κ B C`,
`F(m̂) > −C/κ + α/κ + arcosh(Bκ/2 + 1)/κ`.

**Formalization Note.** `C > 0` is the model's; the two premises quoted ("note first …",
"(16)") are the milestone `eq_16_lower_bound`. -/
theorem eq_17_lower_bound_min (B C α κ : ℝ) (hB : 0 < B) (hC : 0 < C) (hα0 : 0 < α)
    (hα1 : α < 1) (hκ : α ^ 2 / (B * (1 - α)) ≤ κ) :
    -C / κ + α / κ + Real.arcosh (B * κ / 2 + 1) / κ
      < uniExcess κ B C (Real.arcosh (B * κ / 2 + 1) / κ) := by sorry

end LightningNetwork.RateBounds
