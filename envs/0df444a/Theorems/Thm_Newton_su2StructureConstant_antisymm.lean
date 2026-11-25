-- Prove2me | Theorems.Thm_Newton_su2StructureConstant_antisymm
-- name    : Newton.su2StructureConstant_antisymm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:58:25.296719+00:00
-- url     : https://prove2.me/theorems/ca7559f7-d7f9-454b-aba6-9184112596f8
-- title:
--   Newton: su2 Structure Constant antisymm
-- statement:
--   su(2) structure constants are totally antisymmetric
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/GellMannMatrices.lean#L498-L501
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/GellMannMatrices.lean#L498-L501

import Definitions.Def_Newton_Gauge_LieAlgebra
import Definitions.Def_Newton_Gauge_GellMannMatrices
set_option autoImplicit false
open Matrix
open Newton

theorem Newton.su2StructureConstant_antisymm (a b c : Fin 3) :
    su2StructureConstant b a c = -su2StructureConstant a b c := by sorry
