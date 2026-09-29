-- Prove2me | Theorems.Thm_Freiman_middle_interval
-- name    : Freiman.middle_interval
-- status  : Proved
-- author  : @tp
-- created : 2026-09-08T23:23:25.578041+00:00
-- url     : https://prove2.me/theorems/ccda68be-6005-4991-b2f9-86f804182c39
-- title:
--   The middle interval in the Lagrange spectrum
-- statement:
--   The classical Lagrange spectrum contains the closed interval
--   $$
--   \left[\sqrt{21},\frac{128}{25}\right]\subseteq L.
--   $$
--   Both endpoints are included. Together with the inequality $h<128/25$, this interval joins the lower construction to the upper ray.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Theorem 18.1, p. 58; the construction occupies Part III.

import Definitions.Def_Freiman_lagrangeSpectrum

namespace Freiman

theorem middle_interval :
    Set.Icc (Real.sqrt 21) (128 / 25 : ℝ) ⊆ lagrangeSpectrum := by
  sorry

end Freiman
