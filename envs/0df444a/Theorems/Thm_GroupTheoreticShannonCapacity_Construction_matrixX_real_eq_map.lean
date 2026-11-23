-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_Construction_matrixX_real_eq_map
-- name    : GroupTheoreticShannonCapacity.Construction.matrixX_real_eq_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:32:29.667741+00:00
-- url     : https://prove2.me/theorems/b4791883-6ec3-486f-9f16-c4893090dfbf
-- title:
--   Construction: matrix X real eq map
-- statement:
--   matrixX_real agrees with matrixX.map when parameters are integers cast to reals
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Construction.lean#L305-L316
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Construction.lean#L305-L316

import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
import Definitions.Def_GroupTheoreticShannonCapacity_Construction
set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.Construction
open Matrix

theorem GroupTheoreticShannonCapacity.Construction.matrixX_real_eq_map (n k b r s : ℕ) :
    matrixX_real n k b r s = (matrixX n k b r s).map (↑· : ℚ → ℝ) := by sorry
