-- Prove2me | Theorems.Thm_Newton_embedSu2_bracket
-- name    : Newton.embedSu2_bracket
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:19:13.035561+00:00
-- url     : https://prove2.me/theorems/2b15edf8-4c7b-4fae-943d-b529e49cbb5f
-- title:
--   Newton: embed Su2 bracket
-- statement:
--   Embedding preserves Lie bracket
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/GellMannMatrices.lean#L589-L671
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/GellMannMatrices.lean#L589-L671

import Definitions.Def_Newton_Gauge_LieAlgebra
import Definitions.Def_Newton_Gauge_GellMannMatrices
set_option autoImplicit false
open Matrix
open Newton

theorem Newton.embedSu2_bracket (A B : SuNAlgebra 2) (N : ℕ) :
    ⁅embedSu2 A N, embedSu2 B N⁆ = embedSu2 ⁅A, B⁆ N := by sorry
