-- Prove2me | Theorems.Thm_Mandelbrot_volume_frontier_mandelbrot_eq_zero
-- name    : Mandelbrot.volume_frontier_mandelbrot_eq_zero
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-13T02:21:39.06825+00:00
-- url     : https://prove2.me/theorems/fb09e69d-3564-4fad-83b7-dbf40a887fee
-- title:
--   The boundary of the Mandelbrot set has zero area
-- statement:
--   **Conjecture.** The boundary $\partial M$ of the Mandelbrot set has zero area:
--
--   $$\lambda_2(\partial M) = 0,$$
--
--   where $\lambda_2$ denotes planar Lebesgue measure.
--
--   This is open, and it is *not* implied by Shishikura's theorem that $\partial M$ has Hausdorff dimension $2$: a set of full Hausdorff dimension may still be null. The conjecture is known to follow from MLC, since local connectivity yields the pinched-disk model, under which $\partial M$ carries no area. The analogous question in the dynamical plane is settled in the negative: Buff and Cheritat constructed quadratic Julia sets of positive area.
-- source:
--   https://mathoverflow.net/questions/37229/ ; https://en.wikipedia.org/wiki/Mandelbrot_set#Local_connectivity

import Definitions.Def_mandelbrot_sets
open Topology Set Function Filter Bornology Metric MeasureTheory

namespace Mandelbrot

/-- **Conjecture**: the boundary of the Mandelbrot set has zero planar Lebesgue measure. -/
theorem volume_frontier_mandelbrot_eq_zero : volume (frontier mandelbrotSet) = 0 := by
  sorry

end Mandelbrot
