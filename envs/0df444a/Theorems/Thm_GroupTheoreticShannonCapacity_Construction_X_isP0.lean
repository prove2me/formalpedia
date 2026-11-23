-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_Construction_X_isP0
-- name    : GroupTheoreticShannonCapacity.Construction.X_isP0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:33:50.507861+00:00
-- url     : https://prove2.me/theorems/d3b43aa2-b07b-4b8b-a040-8bc970ec705c
-- title:
--   Construction: X is P0
-- statement:
--   X is a P₀-matrix under appropriate conditions
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Construction.lean#L967-L973
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Construction.lean#L967-L973

import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
import Definitions.Def_GroupTheoreticShannonCapacity_Construction
set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.Construction
open Matrix

theorem GroupTheoreticShannonCapacity.Construction.X_isP0 (n : ℕ) (k b r s : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hb : 1 ≤ b)
    (hrb : r ≤ b) :
    P0Matrix.IsP0Matrix n ((matrixX n k b r s).map (↑· : ℚ → ℝ)) := by sorry
