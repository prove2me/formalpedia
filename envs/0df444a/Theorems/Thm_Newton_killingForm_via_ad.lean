-- Prove2me | Theorems.Thm_Newton_killingForm_via_ad
-- name    : Newton.killingForm_via_ad
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:06:42.775595+00:00
-- url     : https://prove2.me/theorems/1f0e510f-ee41-469a-adb0-72074a22defe
-- title:
--   Newton: killing Form via ad
-- statement:
--   Killing form expressed via ad action
--
--   The relation B(X, Y) = Tr(XY) holds.
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/StructureConstants.lean#L98-L99
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/StructureConstants.lean#L98-L99

import Definitions.Def_Newton_Gauge_LieAlgebra
import Definitions.Def_Newton_Gauge_StructureConstants
set_option autoImplicit false
open Matrix
open Newton
variable {N : ℕ}

theorem Newton.killingForm_via_ad [DecidableEq (Fin N)] (A B : SuNAlgebra N) :
    killingForm A B = trace (A.matrix * B.matrix) := by sorry
