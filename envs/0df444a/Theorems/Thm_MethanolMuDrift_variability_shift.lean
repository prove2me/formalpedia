-- Prove2me | Theorems.Thm_MethanolMuDrift_variability_shift
-- name    : MethanolMuDrift.variability_shift
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-05T00:40:18.67805+00:00
-- url     : https://prove2.me/theorems/9d7a3dbe-44ef-4e35-8051-f9161c093989
-- title:
--   Shift of the $0_0$–$1_0\,A^+$ line between epochs: $0.48\pm0.26$ km/s
-- statement:
--   The strong $0_0$–$1_0\,A^+$ line was measured at $8.32\pm0.10$ km/s in December 2011 and at $8.80\pm0.24$ km/s in April 2012. The difference and its uncertainty (errors added in quadrature) are
--   $$8.80-8.32=0.48,\qquad\sqrt{0.24^2+0.10^2}=0.26,$$
--   i.e. $0.48\pm0.26$ km/s — the "possibly indicative" systematic shift due to time variability of the background source, which the authors convert into the conservative systematic uncertainty $7.0\times10^{-8}$ on $\Delta\mu/\mu$.
--
--   **Formalization Note** The two epoch positions are not part of Table 1 and are written directly into the statement.
-- source:
--   J. Bagdonaite, P. Jansen, C. Henkel, H. L. Bethlem, K. M. Menten, W. Ubachs, "A Stringent Limit on a Drifting Proton-to-Electron Mass Ratio from Alcohol in the Early Universe", Science (First Release, 13 December 2012), doi:10.1126/science.1224898, https://doi.org/10.1126/science.1224898, p. 2 (right column): "The strong (0_0-1_0 A+) line ... is positioned at 8.32 ± 0.10 km/s, and at 8.80 ± 0.24 km/s in the spectrum from April 2012. The difference between them is 0.48 ± 0.26 km/s".

import Mathlib
import Definitions.Def_Bagdonaite2013_MethanolMuDrift

namespace MethanolMuDrift

theorem variability_shift :
    (8.80 : ℝ) - 8.32 = 0.48 ∧ Real.sqrt ((0.24 : ℝ) ^ 2 + 0.10 ^ 2) = 0.26 := by sorry

end MethanolMuDrift
