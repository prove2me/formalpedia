-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_Construction_p_over_q_le_a_over_b
-- name    : GroupTheoreticShannonCapacity.Construction.p_over_q_le_a_over_b
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:32:22.365379+00:00
-- url     : https://prove2.me/theorems/d252367c-3fb0-40a2-8021-78ada5e45035
-- title:
--   Construction: p over q le a over b
-- statement:
--   (iii) If b, k > 0 and r, s ≥ 0, then p/q ≤ a/b
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Construction.lean#L190-L264
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Construction.lean#L190-L264

import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
import Definitions.Def_GroupTheoreticShannonCapacity_Construction
set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.Construction
open Matrix

theorem GroupTheoreticShannonCapacity.Construction.p_over_q_le_a_over_b (n : ℕ) (k b r s : ℤ) (hn : 1 ≤ n) (hk : 0 < k) (hb : 0 < b)
    (hr : 0 ≤ r) (hs : 0 ≤ s) :
    p n k b r s / q n k b r s ≤ a n k b r s / b := by sorry
