-- Prove2me | Theorems.Thm_Newton_su2_bracket_31
-- name    : Newton.su2_bracket_31
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:47:10.926048+00:00
-- url     : https://prove2.me/theorems/befb19c1-1467-4a77-bd26-21ff8dead25f
-- title:
--   Newton: su2 bracket 31
-- statement:
--   [T₃, T₁] = T₂
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/GellMannMatrices.lean#L372-L387
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/GellMannMatrices.lean#L372-L387

import Definitions.Def_Newton_Gauge_LieAlgebra
import Definitions.Def_Newton_Gauge_GellMannMatrices
set_option autoImplicit false
open Matrix
open Newton

theorem Newton.su2_bracket_31 : ⁅su2Gen3, su2Gen1⁆ = su2Gen2 := by sorry
