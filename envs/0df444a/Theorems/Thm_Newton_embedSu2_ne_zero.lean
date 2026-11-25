-- Prove2me | Theorems.Thm_Newton_embedSu2_ne_zero
-- name    : Newton.embedSu2_ne_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:19:23.696276+00:00
-- url     : https://prove2.me/theorems/a27a27df-05fe-4c82-8352-4e0c8d06445a
-- title:
--   Newton: embed Su2 ne zero
-- statement:
--   Embedding preserves nonzero elements
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/GellMannMatrices.lean#L674-L688
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/GellMannMatrices.lean#L674-L688

import Definitions.Def_Newton_Gauge_LieAlgebra
import Definitions.Def_Newton_Gauge_GellMannMatrices
set_option autoImplicit false
open Matrix
open Newton

theorem Newton.embedSu2_ne_zero (A : SuNAlgebra 2) (hA : A ≠ 0) (N : ℕ) :
    embedSu2 A N ≠ 0 := by sorry
