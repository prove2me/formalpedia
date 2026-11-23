-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_Construction_X_isP0_s_ne_zero
-- name    : GroupTheoreticShannonCapacity.Construction.X_isP0_s_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:33:45.331575+00:00
-- url     : https://prove2.me/theorems/9ce0dc98-58d5-44a9-97dd-f9b6883f3312
-- title:
--   Construction: X is P0 s ne zero
-- statement:
--   X is a P₀-matrix when s ≠ 0
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Construction.lean#L689-L740
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Construction.lean#L689-L740

import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
import Definitions.Def_GroupTheoreticShannonCapacity_Construction
set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.Construction
open Matrix

theorem GroupTheoreticShannonCapacity.Construction.X_isP0_s_ne_zero (n : ℕ) (k b r s : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hb : 1 ≤ b)
    (hrb : r ≤ b) (hs : s ≠ 0) :
    P0Matrix.IsP0Matrix n ((matrixX n k b r s).map (↑· : ℚ → ℝ)) := by sorry
