-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_Construction_matrixX_real_continuous_s
-- name    : GroupTheoreticShannonCapacity.Construction.matrixX_real_continuous_s
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:32:47.03417+00:00
-- url     : https://prove2.me/theorems/9bbd5a81-2023-4bc1-a1a5-d8b7b5eb183d
-- title:
--   Construction: matrix X real continuous s
-- statement:
--   matrixX_real is continuous in s
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Construction.lean#L319-L340
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Construction.lean#L319-L340

import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
import Definitions.Def_GroupTheoreticShannonCapacity_Construction
set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.Construction
open Matrix

theorem GroupTheoreticShannonCapacity.Construction.matrixX_real_continuous_s (n : ℕ) (k b r : ℝ) :
    Continuous (fun s => matrixX_real n k b r s) := by sorry
