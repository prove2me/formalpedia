-- Prove2me | Theorems.Thm_Freiman_upper_ray
-- name    : Freiman.upper_ray
-- status  : Proved
-- author  : @tp
-- created : 2026-09-08T23:23:38.468623+00:00
-- url     : https://prove2.me/theorems/4347a881-a7ea-4fd3-984e-4e1f5a208201
-- title:
--   The upper ray in the Lagrange spectrum
-- statement:
--   Let $h=(21+\sqrt{21})/5$. Every real number at least $h$ belongs to the classical Lagrange spectrum:
--   $$
--   [h,\infty)\subseteq L.
--   $$
--   The endpoint $h$ is included. This supplies the unbounded part of the Hall ray.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Theorem 19.3, p. 64; the construction occupies Part IV.

import Definitions.Def_Freiman_lagrangeSpectrum
import Definitions.Def_Freiman_gapThreshold

namespace Freiman

theorem upper_ray :
    Set.Ici upperRayStart ⊆ lagrangeSpectrum := by
  sorry

end Freiman
