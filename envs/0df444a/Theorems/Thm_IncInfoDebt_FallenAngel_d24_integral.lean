-- Prove2me | Theorems.Thm_IncInfoDebt_FallenAngel_d24_integral
-- name    : IncInfoDebt.FallenAngel.d24_integral
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:18:18.045837+00:00
-- url     : https://prove2.me/theorems/3fdf8eae-464d-4142-a342-9a7769fadd4d
-- title:
--   Equation (D.24) — Gaussian upper-tail integral
-- statement:
--   Write $N$ for the standard normal cumulative distribution function. The Gaussian upper-tail integral in the proof of Corollary 1 has the exact value
--
--   $$\int_0^\infty \alpha N(-\alpha)\,d\alpha=\frac14.$$
--
--   This constant fixes the factor in the default-intensity boundary formula (D.25). The integral is a genuine finite integral on the positive half-line.
-- source:
--   Benzoni, Garlappi & Goldstein, Federal Reserve Bank of Chicago WP 2019-08 (20 Sept 2019), Online Appendix p. 18, proof of Corollary 1, (D.24), https://doi.org/10.21033/wp-2019-08

import Mathlib
import Definitions.Def_IncInfoDebt_FallenAngel_Model

namespace IncInfoDebt.FallenAngel
open MeasureTheory

/-- Equation (D.24), Online Appendix p. 18. -/
theorem d24_integral :
    (∫ α in Set.Ioi (0 : ℝ), α * N (-α)) = (1 / 4 : ℝ) := by sorry

end IncInfoDebt.FallenAngel
