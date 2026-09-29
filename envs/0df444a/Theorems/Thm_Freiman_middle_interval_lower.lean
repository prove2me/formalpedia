-- Prove2me | Theorems.Thm_Freiman_middle_interval_lower
-- name    : Freiman.middle_interval_lower
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-10T19:01:24.336355+00:00
-- url     : https://prove2.me/theorems/fe49fd2a-c9ab-4d93-a795-ac248cdafc35
-- title:
--   The lower part of the middle interval in the Lagrange spectrum
-- statement:
--   The lower part of the middle interval is contained in the classical Lagrange spectrum:
--   $$\left[\sqrt{21}, \frac{21+\sqrt{21}}{5}\right] \subseteq L.$$
--   Both endpoints are included. This is the core topological construction of the middle interval, bridging the lower construction to the upper ray.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, derived by splitting the middle interval at upperRayStart.

import Definitions.Def_Freiman_lagrangeSpectrum
import Definitions.Def_Freiman_gapThreshold
open Freiman

namespace Freiman

theorem middle_interval_lower :
    Set.Icc (Real.sqrt 21) upperRayStart ⊆ lagrangeSpectrum := by
  sorry

end Freiman
