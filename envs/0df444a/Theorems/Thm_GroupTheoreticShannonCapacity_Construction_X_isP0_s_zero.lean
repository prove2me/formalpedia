-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_Construction_X_isP0_s_zero
-- name    : GroupTheoreticShannonCapacity.Construction.X_isP0_s_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:34:01.285794+00:00
-- url     : https://prove2.me/theorems/5e33c62d-25f0-4bb1-8bc1-7c1676602a70
-- title:
--   Construction: X is P0 s zero
-- statement:
--   X is a P₀-matrix when s = 0, using the closure of the P₀ property
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Construction.lean#L927-L964
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Construction.lean#L927-L964

import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
import Definitions.Def_GroupTheoreticShannonCapacity_Construction
set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.Construction
open Matrix

theorem GroupTheoreticShannonCapacity.Construction.X_isP0_s_zero (n : ℕ) (k b r : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hb : 1 ≤ b)
    (hrb : r ≤ b) :
    P0Matrix.IsP0Matrix n ((matrixX n k b r 0).map (↑· : ℚ → ℝ)) := by sorry
