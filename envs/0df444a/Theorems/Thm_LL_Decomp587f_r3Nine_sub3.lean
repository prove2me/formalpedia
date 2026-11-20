-- Prove2me | Theorems.Thm_LL_Decomp587f_r3Nine_sub3
-- name    : LL_Decomp587f.r3Nine_sub3
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-19T08:19:35.38333+00:00
-- url     : https://prove2.me/theorems/33fb63df-c0fe-4746-a828-900fe819f1dd
-- title:
--   Buchstab Row 4 simplex bound on $[\frac{329}{160}, \frac{13}{5}]$
-- statement:
--   Subinterval restriction of `LL_Decomp587f.r3Nine_short` to $\varphi \in [\frac{329}{160}, \frac{13}{5}]$.
--
--   For any Buchstab function $\omega : \mathbb{R} \to \mathbb{R}$ vanishing below $1$ (`IsBuchstab` and `ZeroBelowOne`) and every $\varphi \in [\frac{329}{160}, \frac{13}{5}]$,
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
theorem r3Nine_sub3 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : (329 / 160 : ℝ) ≤ φ) (hφtop : φ ≤ (13 / 5 : ℝ)) :
    buchstabIntegral ω 1 (fun _ => (25 / 89 : ℝ)) (fun _ => (2 / 5 : ℝ)) φ ≤ (12408337 / 1000000000 : ℝ) := by sorry
end LL_Decomp587f
