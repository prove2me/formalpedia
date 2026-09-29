-- Prove2me | Theorems.Thm_Freiman_lower_interval
-- name    : Freiman.lower_interval
-- status  : Proved
-- author  : @tp
-- created : 2026-09-08T23:23:14.782895+00:00
-- url     : https://prove2.me/theorems/4c9b477a-4ba3-4e1b-90db-b2fb1a5bb49e
-- title:
--   The lower interval in the Lagrange spectrum
-- statement:
--   Every real number between Freiman's constant and $\sqrt{21}$ belongs to the classical Lagrange spectrum:
--   $$
--   [c_F,\sqrt{21}]\subseteq L.
--   $$
--   Both endpoints are included. This is the conclusion of the lower interval construction.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Theorem 9.2, pp. 48–49, its interval inclusion conclusion; the construction occupies Part II.

import Definitions.Def_Freiman_cF
import Definitions.Def_Freiman_lagrangeSpectrum

namespace Freiman

theorem lower_interval :
    Set.Icc cF (Real.sqrt 21) ⊆ lagrangeSpectrum := by
  sorry

end Freiman
