-- Prove2me | Theorems.Thm_Newton_su2_has_noncommuting_pair
-- name    : Newton.su2_has_noncommuting_pair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:18:42.177831+00:00
-- url     : https://prove2.me/theorems/0cf5007c-5c78-408e-be96-8dfa36da8d91
-- title:
--   Newton: su2 has noncommuting pair
-- statement:
--   For N = 2, su(2) has noncommuting elements
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/GellMannMatrices.lean#L504-L506
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/GellMannMatrices.lean#L504-L506

import Definitions.Def_Newton_Gauge_LieAlgebra
import Definitions.Def_Newton_Gauge_GellMannMatrices
set_option autoImplicit false
open Matrix
open Newton

theorem Newton.su2_has_noncommuting_pair :
    ∃ (A B : SuNAlgebra 2), ⁅A, B⁆ ≠ 0 := by sorry
