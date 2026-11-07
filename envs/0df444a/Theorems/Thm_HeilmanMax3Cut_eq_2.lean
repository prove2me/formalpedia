-- Prove2me | Theorems.Thm_HeilmanMax3Cut_eq_2
-- name    : HeilmanMax3Cut.eq_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:29:05.547449+00:00
-- url     : https://prove2.me/theorems/316a62f6-078b-4dcd-9337-6a1eb2aaacb4
-- title:
--   Eq. (2) — $\alpha_3$ is attained at $\rho=-1/2$, $\alpha_3\approx.83600811464$
-- statement:
--   The Frieze–Jerrum constant satisfies
--
--   $$\alpha_3=\inf_{-1/2\le\rho<1}\frac{\tfrac32\bigl[1-3\bigl(\tfrac19+\frac{[\arccos(-\rho)]^2-[\arccos(\rho/2)]^2}{4\pi^2}\bigr)\bigr]}{1-\rho}=\frac{\tfrac32\bigl[1-3\bigl(\tfrac19+\frac{[\arccos(1/2)]^2-[\arccos(-1/4)]^2}{4\pi^2}\bigr)\bigr]}{1+1/2},$$
--
--   so the infimum is attained at $\rho=-1/2$, and $|\alpha_3-0.83600811464|<5\cdot10^{-12}$.
--
--   It identifies the hardness ratio produced at $\rho=-1/2$ with the approximation ratio of the Frieze–Jerrum algorithm.
--
--   Differences from the source:
--   - encoding: infimum over −1/2 ≤ ρ ≤ 1 → infimum over [−1/2, 1); reason: at ρ = 1 the fraction is 0/0 (undefined); the ratio tends to +∞ as ρ → 1⁻
--   - reading: ≈ .83600811464 → |α₃ − 0.83600811464| < 5·10⁻¹²; reason: agreement to the eleven printed digits (half a unit in the last place); the true value is 0.83600811464261…
-- source:
--   Heilman, Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT, arXiv:2608.00333 (held version, sha256 2b4f1d11…), Eq. (2), p.3

import Mathlib
import Definitions.Def_HeilmanMax3Cut_alpha3
open Real

namespace HeilmanMax3Cut

/-- **Eq. (2): the value of `α₃`.** Heilman, *Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT*, arXiv:2608.00333 (held version,
sha256 2b4f1d11…), Eq. (2), p.3:
`α₃ := inf_{−1/2 ≤ ρ ≤ 1} (3/2)[1 − 3(1/9 + ([arccos(−ρ)]² − [arccos(ρ/2)]²)/(4π²))]/(1 − ρ)
= (3/2)[1 − 3(1/9 + ([arccos(1/2)]² − [arccos(−1/4)]²)/(4π²))]/(1 + 1/2) ≈ .83600811464`.

Both claims are stated: the infimum is attained at `ρ = −1/2` (it equals the printed value of the
ratio there), and that value agrees with `.83600811464` to the printed eleven digits.

**Formalization Note.** `α₃` is `alpha3` (infimum over `[−1/2, 1)`; `ρ = 1` gives `0/0`). "≈" is read
as `|α₃ − 0.83600811464| < 5·10⁻¹²` (half a unit in the last printed digit; the true value is
`0.83600811464261…`). -/
theorem eq_2 :
    alpha3 = (3 / 2) * (1 - 3 * (1 / 9 +
        (Real.arccos (1 / 2) ^ 2 - Real.arccos (-1 / 4) ^ 2) / (4 * π ^ 2))) / (1 + 1 / 2) ∧
    |alpha3 - 0.83600811464| < 5 / 10 ^ 12 := by sorry

end HeilmanMax3Cut
