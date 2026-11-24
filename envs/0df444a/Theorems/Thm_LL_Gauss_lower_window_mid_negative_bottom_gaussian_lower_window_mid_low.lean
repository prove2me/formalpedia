-- Prove2me | Theorems.Thm_LL_Gauss_lower_window_mid_negative_bottom_gaussian_lower_window_mid_low
-- name    : LL_Gauss_lower_window_mid.negative_bottom_gaussian_lower_window_mid_low
-- status  : Proved
-- author  : @sthubbar
-- created : 2026-11-20T08:04:28.769936+00:00
-- url     : https://prove2.me/theorems/8a6f7931-2047-44ea-a874-45c6ec65a338
-- title:
--   Modulus comparison for $F_\delta$ on $1/2+it$, $-23/16\le t\le-17/12$
-- statement:
--   For every real $\delta$ and every real $t$ with $-23/16\le t\le -17/12$, one has $|F_\delta(\tfrac12+it)|\le 2\,|F_\delta(\tfrac12-i)|$, where $F_\delta(s)=\int_0^\infty u^{s-1}e^{-u^2/2}e^{2\pi i\delta u}\,du$ is the Mellin transform defined above.
-- source:
--   H. A. Helfgott, Major arcs for Goldbach's problem, arXiv 1305.2897, the Gaussian Mellin transform $F_\delta$ of display 4.42 to 4.43, page 43.

import Mathlib
import Definitions.Def_LL_Gauss_lower_window_mid_e
import Definitions.Def_LL_Gauss_lower_window_mid_gaussianMellin

open Real

namespace LL_Gauss_lower_window_mid
theorem negative_bottom_gaussian_lower_window_mid_low (δ : ℝ) {t : ℝ}
    (hlo : -(23 / 16) ≤ t) (hhi : t ≤ -(17 / 12)) :
    ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ≤
      2 * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ := by sorry
end LL_Gauss_lower_window_mid
