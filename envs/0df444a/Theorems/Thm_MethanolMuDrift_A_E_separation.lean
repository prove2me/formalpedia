-- Prove2me | Theorems.Thm_MethanolMuDrift_A_E_separation
-- name    : MethanolMuDrift.A_E_separation
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-05T00:16:16.117529+00:00
-- url     : https://prove2.me/theorems/50380631-1db2-4011-aeac-06a3a0d0ecd2
-- title:
--   The $0_0$–$1_0$ $A^+$ and $E$ lines are separated by $0.72\pm0.32$ km/s
-- statement:
--   In Table 1 the $0_0$–$1_0\,E$ line is at $9.12\pm0.30$ km/s and the $0_0$–$1_0\,A^+$ line at $8.40\pm0.10$ km/s. Their separation and its uncertainty (independent errors added in quadrature) are
--   $$9.12-8.40=0.72,\qquad \Big|\sqrt{0.30^2+0.10^2}-0.32\Big|\le0.005,$$
--   i.e. the two lines are separated by $0.72\pm0.32$ km/s. Together with the larger E linewidths, this is the evidence for spatial segregation of E- and A-symmetry methanol that led the authors to adopt the E-only fit as fiducial.
--
--   **Formalization Note** Positions and uncertainties are read from the definition file's Table 1 arrays (indices 2 and 1); the quadrature rule for the uncertainty of a difference is the reading of "$\pm0.32$" used here.
-- source:
--   J. Bagdonaite, P. Jansen, C. Henkel, H. L. Bethlem, K. M. Menten, W. Ubachs, "A Stringent Limit on a Drifting Proton-to-Electron Mass Ratio from Alcohol in the Early Universe", Science (First Release, 13 December 2012), doi:10.1126/science.1224898, https://doi.org/10.1126/science.1224898, p. 2 (right column): "In the combined spectrum the 0_0-1_0 A+ and 0_0-1_0 E transitions ... are separated by 0.72 ± 0.32 km/s."; Table 1, p. 4.

import Mathlib
import Definitions.Def_Bagdonaite2013_MethanolMuDrift

namespace MethanolMuDrift

theorem A_E_separation :
    allV 2 - allV 1 = 0.72 ∧
      |Real.sqrt (allSigma 2 ^ 2 + allSigma 1 ^ 2) - 0.32| ≤ 0.005 := by sorry

end MethanolMuDrift
