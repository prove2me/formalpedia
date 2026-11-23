-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_Construction_p_q_are_integers
-- name    : GroupTheoreticShannonCapacity.Construction.p_q_are_integers
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:27:00.670809+00:00
-- url     : https://prove2.me/theorems/ffb0fb9e-813f-4f5e-b96c-9a3c90ce3d13
-- title:
--   Construction: p q are integers
-- statement:
--   p and q are integers when parameters are nonnegative integers
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Construction.lean#L123-L144
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Construction.lean#L123-L144

import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
import Definitions.Def_GroupTheoreticShannonCapacity_Construction
set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.Construction
open Matrix

theorem GroupTheoreticShannonCapacity.Construction.p_q_are_integers (n k b r s : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hb : 1 ≤ b) :
    ∃ (p' q' : ℤ), p n k b r s = p' ∧ q n k b r s = q' := by sorry
