-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_Construction_denom_ne_zero_nat
-- name    : GroupTheoreticShannonCapacity.Construction.denom_ne_zero_nat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:34:41.24872+00:00
-- url     : https://prove2.me/theorems/ca37c0f8-a30c-41b1-a097-2546ff943b5b
-- title:
--   Construction: denom ne zero nat
-- statement:
--   For natural number parameters with k ≥ 1 and b ≥ 1, the denominator is nonzero.
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Construction.lean#L1661-L1663
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Construction.lean#L1661-L1663

import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
import Definitions.Def_GroupTheoreticShannonCapacity_Construction
set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.Construction
open Matrix

theorem GroupTheoreticShannonCapacity.Construction.denom_ne_zero_nat (n k b r : ℕ) (hk : 1 ≤ k) (hb : 1 ≤ b) :
    (r : ℤ) + (k : ℤ) * (b : ℤ) ^ n ≠ 0 := by sorry
