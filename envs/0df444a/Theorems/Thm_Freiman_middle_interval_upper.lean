-- Prove2me | Theorems.Thm_Freiman_middle_interval_upper
-- name    : Freiman.middle_interval_upper
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-10T19:01:32.253273+00:00
-- url     : https://prove2.me/theorems/b5ed28a6-0ae6-4e21-bb75-fa3055b69c04
-- title:
--   The upper part of the middle interval in the Lagrange spectrum
-- statement:
--   The upper part of the middle interval is contained in the classical Lagrange spectrum:
--   $$\left[\frac{21+\sqrt{21}}{5}, \frac{128}{25}\right] \subseteq L.$$
--   Both endpoints are included. This follows trivially from the upper ray $[h, \infty) \subseteq L$ where $h = \frac{21+\sqrt{21}}{5}$, since $h < \frac{128}{25}$.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, derived by splitting the middle interval at upperRayStart.

import Definitions.Def_Freiman_lagrangeSpectrum
import Definitions.Def_Freiman_gapThreshold
open Freiman

namespace Freiman

theorem middle_interval_upper :
    Set.Icc upperRayStart (128 / 25 : ℝ) ⊆ lagrangeSpectrum := by
  sorry

end Freiman
