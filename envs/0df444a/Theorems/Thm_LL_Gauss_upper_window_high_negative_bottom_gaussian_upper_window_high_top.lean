-- Prove2me | Theorems.Thm_LL_Gauss_upper_window_high_negative_bottom_gaussian_upper_window_high_top
-- name    : LL_Gauss_upper_window_high.negative_bottom_gaussian_upper_window_high_top
-- status  : Open
-- author  : @sthubbar
-- created : 2026-11-20T07:49:55.41816+00:00
-- url     : https://prove2.me/theorems/1befd706-94e2-4854-ab8a-29d7ac6b14af
-- title:
--   Modulus comparison for $F_\delta$ on $1/2+it$, $-65/64\le t\le-1$
-- statement:
--   For every real $\delta$ and every real $t$ with $-65/64\le t\le -1$, one has $|F_\delta(\tfrac12+it)|\le 3/2\,|F_\delta(\tfrac12-i)|$, where $F_\delta(s)=\int_0^\infty u^{s-1}e^{-u^2/2}e^{2\pi i\delta u}\,du$ is the Mellin transform defined above.
-- source:
--   H. A. Helfgott, Major arcs for Goldbach's problem, arXiv 1305.2897, the Gaussian Mellin transform $F_\delta$ of display 4.42 to 4.43, page 43.

import Mathlib
import Definitions.Def_LL_Gauss_upper_window_high_e
import Definitions.Def_LL_Gauss_upper_window_high_gaussianMellin

open Real

namespace LL_Gauss_upper_window_high
theorem negative_bottom_gaussian_upper_window_high_top (δ : ℝ) {t : ℝ}
    (hlo : -(65 / 64) ≤ t) (hhi : t ≤ -1) :
    ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ≤
      (3 / 2) * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ := by sorry
end LL_Gauss_upper_window_high
