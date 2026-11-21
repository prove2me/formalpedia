-- Prove2me | Theorems.Thm_LL_Gauss_lower_window_high_negative_bottom_gaussian_lower_window_high_large_delta_high
-- name    : LL_Gauss_lower_window_high.negative_bottom_gaussian_lower_window_high_large_delta_high
-- status  : Open
-- author  : @sthubbar
-- created : 2026-11-20T08:00:30.793544+00:00
-- url     : https://prove2.me/theorems/6723a49e-1d05-4827-8c9d-6b142c5df390
-- title:
--   Modulus comparison for $F_\delta$ on $1/2+it$, $-21/16\le t\le-5/4$, large $|\delta|$
-- statement:
--   For every real $\delta$ with $|\delta|\ge1$ and every real $t$ with $-21/16\le t\le -5/4$, one has $|F_\delta(\tfrac12+it)|\le 2\,|F_\delta(\tfrac12-i)|$, where $F_\delta(s)=\int_0^\infty u^{s-1}e^{-u^2/2}e^{2\pi i\delta u}\,du$ is the Mellin transform defined above.
-- source:
--   H. A. Helfgott, Major arcs for Goldbach's problem, arXiv 1305.2897, the Gaussian Mellin transform $F_\delta$ of display 4.42 to 4.43, page 43.

import Mathlib
import Definitions.Def_LL_Gauss_lower_window_high_e
import Definitions.Def_LL_Gauss_lower_window_high_gaussianMellin

open Real

namespace LL_Gauss_lower_window_high
theorem negative_bottom_gaussian_lower_window_high_large_delta_high (δ : ℝ) (hδ : 1 ≤ |δ|)
    {t : ℝ} (hlo : -(21 / 16) ≤ t) (hhi : t ≤ -(5 / 4)) :
    ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ≤
      2 * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ := by sorry
end LL_Gauss_lower_window_high
