-- Prove2me | Theorems.Thm_LL_Gauss_upper_window_high_negative_bottom_gaussian_upper_window_high_mid
-- name    : LL_Gauss_upper_window_high.negative_bottom_gaussian_upper_window_high_mid
-- status  : Open
-- author  : @sthubbar
-- created : 2026-11-20T07:48:43.565502+00:00
-- url     : https://prove2.me/theorems/750d70a5-007a-41df-8528-a1fde6cf0e1c
-- title:
--   Modulus comparison for $F_\delta$ on $1/2+it$, $-67/64\le t\le-33/32$
-- statement:
--   For every real $\delta$ and every real $t$ with $-67/64\le t\le -33/32$, one has $|F_\delta(\tfrac12+it)|\le 3/2\,|F_\delta(\tfrac12-i)|$, where $F_\delta(s)=\int_0^\infty u^{s-1}e^{-u^2/2}e^{2\pi i\delta u}\,du$ is the Mellin transform defined above.
-- source:
--   H. A. Helfgott, Major arcs for Goldbach's problem, arXiv 1305.2897, the Gaussian Mellin transform $F_\delta$ of display 4.42 to 4.43, page 43.

import Mathlib
import Definitions.Def_LL_Gauss_upper_window_high_e
import Definitions.Def_LL_Gauss_upper_window_high_gaussianMellin

open Real

namespace LL_Gauss_upper_window_high
theorem negative_bottom_gaussian_upper_window_high_mid (δ : ℝ) {t : ℝ}
    (hlo : -(67 / 64) ≤ t) (hhi : t ≤ -(33 / 32)) :
    ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ≤
      (3 / 2) * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ := by sorry
end LL_Gauss_upper_window_high
