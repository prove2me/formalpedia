-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_Construction_R_sub_bI_isUnit
-- name    : GroupTheoreticShannonCapacity.Construction.R_sub_bI_isUnit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:27:06.15733+00:00
-- url     : https://prove2.me/theorems/708b5f72-ca6e-4551-94f8-cb8394ce1096
-- title:
--   Construction: R sub b I is Unit
-- statement:
--   R - b•I is invertible when r + k*b^n ≠ 0 (for natural number parameters)
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Construction.lean#L1044-L1060
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Construction.lean#L1044-L1060

import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
import Definitions.Def_GroupTheoreticShannonCapacity_Construction
set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.Construction
open Matrix

theorem GroupTheoreticShannonCapacity.Construction.R_sub_bI_isUnit (n k b r : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hd : (r : ℤ) + (k : ℤ) * (b : ℤ) ^ n ≠ 0) :
    IsUnit (MAlpha.Rα n ((r : ℝ) / (k : ℝ)) - (b : ℝ) • 1) := by sorry
