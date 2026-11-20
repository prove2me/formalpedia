-- Prove2me | Theorems.Thm_LL_Decomp587f_r3Nine_sub0
-- name    : LL_Decomp587f.r3Nine_sub0
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-19T08:19:21.499527+00:00
-- url     : https://prove2.me/theorems/57c004f2-0d7a-4895-8815-485619164a04
-- title:
--   Buchstab Row 4 simplex bound on $[2, \frac{649}{320}]$
-- statement:
--   Subinterval restriction of `LL_Decomp587f.r3Nine_short` to $\varphi \in [2, \frac{649}{320}]$.
--
--   For any Buchstab function $\omega : \mathbb{R} \to \mathbb{R}$ vanishing below $1$ (`IsBuchstab` and `ZeroBelowOne`) and every $\varphi \in [2, \frac{649}{320}]$,
--
--   $$
--   \int_{25/89}^{2/5} \int_{x_0}^{2/5} \int_{x_1}^{2/5} \frac{\omega\!\left(\frac{\varphi - x_0 - x_1 - x_2}{x_1}\right)}{x_0 x_1^2 x_2}\, dx_2\, dx_1\, dx_0 \le \frac{12408337}{1000000000}.
--   $$
-- source:
--   Wu Buchstab Row 4 (`LL_Decomp587f.r3Nine_short`) subinterval decomposition over φ ∈ [2, 13/5]

import Mathlib
import Definitions.Def_LL_Decomp587f_IsBuchstab
import Definitions.Def_LL_Decomp587f_ZeroBelowOne
import Definitions.Def_LL_Decomp587f_buchstabIntegral

open Real Set MeasureTheory

namespace LL_Decomp587f
theorem r3Nine_sub0 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : (2 : ℝ) ≤ φ) (hφtop : φ ≤ (649 / 320 : ℝ)) :
    buchstabIntegral ω 1 (fun _ => (25 / 89 : ℝ)) (fun _ => (2 / 5 : ℝ)) φ ≤ (12408337 / 1000000000 : ℝ) := by sorry
end LL_Decomp587f
