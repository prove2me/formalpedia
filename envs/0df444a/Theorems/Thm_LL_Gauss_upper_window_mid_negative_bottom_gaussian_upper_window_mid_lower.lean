-- Prove2me | Theorems.Thm_LL_Gauss_upper_window_mid_negative_bottom_gaussian_upper_window_mid_lower
-- name    : LL_Gauss_upper_window_mid.negative_bottom_gaussian_upper_window_mid_lower
-- status  : Proved
-- author  : @sthubbar
-- created : 2026-11-20T07:57:16.045931+00:00
-- url     : https://prove2.me/theorems/ccad5a79-1f91-46e7-bccd-4c6c5e339be3
-- title:
--   Modulus comparison for $F_\delta$ on $1/2+it$, $-9/8\le t\le-53/48$
-- statement:
--   For every real $\delta$ and every real $t$ with $-9/8\le t\le -53/48$, one has $|F_\delta(\tfrac12+it)|\le 3/2\,|F_\delta(\tfrac12-i)|$, where $F_\delta(s)=\int_0^\infty u^{s-1}e^{-u^2/2}e^{2\pi i\delta u}\,du$ is the Mellin transform defined above.
-- source:
--   H. A. Helfgott, Major arcs for Goldbach's problem, arXiv 1305.2897, the Gaussian Mellin transform $F_\delta$ of display 4.42 to 4.43, page 43.

import Mathlib
import Definitions.Def_LL_Gauss_upper_window_mid_e
import Definitions.Def_LL_Gauss_upper_window_mid_gaussianMellin

open Real

namespace LL_Gauss_upper_window_mid
theorem negative_bottom_gaussian_upper_window_mid_lower (δ : ℝ) {t : ℝ}
    (hlo : -(9 / 8) ≤ t) (hhi : t ≤ -(53 / 48)) :
    ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ≤
      (3 / 2) * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ := by sorry
end LL_Gauss_upper_window_mid
