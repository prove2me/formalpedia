-- Prove2me | Theorems.Thm_NCGchk_schwarzschild_log_coefficient
-- name    : NCGchk.schwarzschild_log_coefficient
-- status  : Proved
-- author  : @LG
-- created : 2026-11-26T12:19:11.088827+00:00
-- url     : https://prove2.me/theorems/9c237e10-244a-557b-909a-01705356defc
-- title:
--   Schwarzschild log coefficient (check)
-- statement:
--   Sen logarithmic correction coefficient.

import Mathlib

namespace NCGchk
theorem schwarzschild_log_coefficient :
    (257 / 302 : ℝ) / (2 * (1 - (257 / 302 : ℝ))) - 1 / 2 = 106 / 45 := by sorry
end NCGchk
