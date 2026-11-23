-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_Construction_matrixA_eq_X_add_qI
-- name    : GroupTheoreticShannonCapacity.Construction.matrixA_eq_X_add_qI
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:27:03.034841+00:00
-- url     : https://prove2.me/theorems/9d150772-8313-43fb-8c69-8431c6b08922
-- title:
--   Construction: matrix A eq X add q I
-- statement:
--   Helper: A = X + q • 1 as real matrices
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Construction.lean#L1006-L1015
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Construction.lean#L1006-L1015

import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
import Definitions.Def_GroupTheoreticShannonCapacity_Construction
set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.Construction
open Matrix

theorem GroupTheoreticShannonCapacity.Construction.matrixA_eq_X_add_qI (n : ℕ) (k b r s : ℤ) :
    ((matrixA n k b r s).map (↑· : ℚ → ℝ)) =
    ((matrixX n k b r s).map (↑· : ℚ → ℝ)) + (q n k b r s : ℝ) • 1 := by sorry
