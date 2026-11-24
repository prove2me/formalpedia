-- Prove2me | Theorems.Thm_LL_Gauss_upper_window_low_negative_bottom_gaussian_upper_window_low_inner
-- name    : LL_Gauss_upper_window_low.negative_bottom_gaussian_upper_window_low_inner
-- status  : Proved
-- author  : @sthubbar
-- created : 2026-11-20T07:53:09.555355+00:00
-- url     : https://prove2.me/theorems/fbb5eef7-9f3b-4807-a279-c955bcc2afba
-- title:
--   Modulus comparison for $F_\delta$ on $1/2+it$, $-19/16\le t\le-9/8$
-- statement:
--   For every real $\delta$ and every real $t$ with $-19/16\le t\le -9/8$, one has $|F_\delta(\tfrac12+it)|\le 3/2\,|F_\delta(\tfrac12-i)|$, where $F_\delta(s)=\int_0^\infty u^{s-1}e^{-u^2/2}e^{2\pi i\delta u}\,du$ is the Mellin transform defined above.
-- source:
--   H. A. Helfgott, Major arcs for Goldbach's problem, arXiv 1305.2897, the Gaussian Mellin transform $F_\delta$ of display 4.42 to 4.43, page 43.

import Mathlib
import Definitions.Def_LL_Gauss_upper_window_low_e
import Definitions.Def_LL_Gauss_upper_window_low_gaussianMellin

open Real

namespace LL_Gauss_upper_window_low
theorem negative_bottom_gaussian_upper_window_low_inner (δ : ℝ) {t : ℝ}
    (hlo : -(19 / 16) ≤ t) (hhi : t ≤ -(9 / 8)) :
    ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ≤
      (3 / 2) * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ := by sorry
end LL_Gauss_upper_window_low
