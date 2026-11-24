-- Prove2me | Theorems.Thm_LL_Gauss_lower_window_high_negative_bottom_gaussian_lower_window_high_large_delta_low
-- name    : LL_Gauss_lower_window_high.negative_bottom_gaussian_lower_window_high_large_delta_low
-- status  : Proved
-- author  : @sthubbar
-- created : 2026-11-20T07:59:44.409206+00:00
-- url     : https://prove2.me/theorems/ce3b214a-ecd8-4b68-8eeb-e88b51d3e02c
-- title:
--   Modulus comparison for $F_\delta$ on $1/2+it$, $-11/8\le t\le-21/16$, large $|\delta|$
-- statement:
--   For every real $\delta$ with $|\delta|\ge1$ and every real $t$ with $-11/8\le t\le -21/16$, one has $|F_\delta(\tfrac12+it)|\le 2\,|F_\delta(\tfrac12-i)|$, where $F_\delta(s)=\int_0^\infty u^{s-1}e^{-u^2/2}e^{2\pi i\delta u}\,du$ is the Mellin transform defined above.
-- source:
--   H. A. Helfgott, Major arcs for Goldbach's problem, arXiv 1305.2897, the Gaussian Mellin transform $F_\delta$ of display 4.42 to 4.43, page 43.

import Mathlib
import Definitions.Def_LL_Gauss_lower_window_high_e
import Definitions.Def_LL_Gauss_lower_window_high_gaussianMellin

open Real

namespace LL_Gauss_lower_window_high
theorem negative_bottom_gaussian_lower_window_high_large_delta_low (δ : ℝ) (hδ : 1 ≤ |δ|)
    {t : ℝ} (hlo : -(11 / 8) ≤ t) (hhi : t ≤ -(21 / 16)) :
    ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ≤
      2 * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ := by sorry
end LL_Gauss_lower_window_high
