-- Prove2me | Theorems.Thm_LL_Gauss_lower_window_high_negative_bottom_gaussian_lower_window_high_small_delta
-- name    : LL_Gauss_lower_window_high.negative_bottom_gaussian_lower_window_high_small_delta
-- status  : Open
-- author  : @sthubbar
-- created : 2026-11-20T08:01:05.25548+00:00
-- url     : https://prove2.me/theorems/6b4e47aa-4925-49b5-b80b-01b256d1c62f
-- title:
--   Modulus comparison for $F_\delta$ on $1/2+it$, $-11/8\le t\le-5/4$, small $|\delta|$
-- statement:
--   For every real $\delta$ with $|\delta|\le1$ and every real $t$ with $-11/8\le t\le -5/4$, one has $|F_\delta(\tfrac12+it)|\le 2\,|F_\delta(\tfrac12-i)|$, where $F_\delta(s)=\int_0^\infty u^{s-1}e^{-u^2/2}e^{2\pi i\delta u}\,du$ is the Mellin transform defined above.
-- source:
--   H. A. Helfgott, Major arcs for Goldbach's problem, arXiv 1305.2897, the Gaussian Mellin transform $F_\delta$ of display 4.42 to 4.43, page 43.

import Mathlib
import Definitions.Def_LL_Gauss_lower_window_high_e
import Definitions.Def_LL_Gauss_lower_window_high_gaussianMellin

open Real

namespace LL_Gauss_lower_window_high
theorem negative_bottom_gaussian_lower_window_high_small_delta (δ : ℝ) (hδ : |δ| ≤ 1)
    {t : ℝ} (hlo : -(11 / 8) ≤ t) (hhi : t ≤ -(5 / 4)) :
    ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ≤
      2 * ‖gaussianMellin δ ((1 / 2 : ℂ) - Complex.I)‖ := by sorry
end LL_Gauss_lower_window_high
