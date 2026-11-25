-- Prove2me | Theorems.Thm_Newton_su2_adjointSq_31
-- name    : Newton.su2_adjointSq_31
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:56:18.146432+00:00
-- url     : https://prove2.me/theorems/da749045-8fd2-47da-97ba-b29d8d7de09e
-- title:
--   Newton: su2 adjoint Sq 31
-- statement:
--   [T₃, [T₃, T₁]] = [T₃, T₂] = -T₁
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/GellMannMatrices.lean#L440-L441
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/GellMannMatrices.lean#L440-L441

import Definitions.Def_Newton_Gauge_LieAlgebra
import Definitions.Def_Newton_Gauge_GellMannMatrices
set_option autoImplicit false
open Matrix
open Newton

theorem Newton.su2_adjointSq_31 : ⁅su2Gen3, ⁅su2Gen3, su2Gen1⁆⁆ = -su2Gen1 := by sorry
