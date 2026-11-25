-- Prove2me | Theorems.Thm_Newton_exists_noncommuting_elements
-- name    : Newton.exists_noncommuting_elements
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:02:14.143688+00:00
-- url     : https://prove2.me/theorems/ed289347-d485-4e4a-b7e2-ab643a61a0d7
-- title:
--   Newton: exists noncommuting elements
-- statement:
--   For N ≥ 2, su(N) has noncommuting elements
--
--   Proof by embedding su(2) into su(N).
--   For N = 2, directly constructed from Pauli matrices.
--   For N > 2, we use embedding of su(2) into the upper-left 2×2 block.
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/GellMannMatrices.lean#L696-L712
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Gauge/GellMannMatrices.lean#L696-L712

import Definitions.Def_Newton_Gauge_LieAlgebra
import Definitions.Def_Newton_Gauge_GellMannMatrices
set_option autoImplicit false
open Matrix
open Newton

theorem Newton.exists_noncommuting_elements (N : ℕ) (hN : N ≥ 2) :
    ∃ (A B : SuNAlgebra N), ⁅A, B⁆ ≠ 0 := by sorry
