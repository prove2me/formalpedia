-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_shannonCapacity_fractionGraph_mono
-- name    : GroupTheoreticShannonCapacity.shannonCapacity_fractionGraph_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:25:58.68258+00:00
-- url     : https://prove2.me/theorems/9e4756ba-9638-46aa-b07e-3b00aeea0cb4
-- title:
--   Group Theoretic Shannon Capacity: shannon Capacity fraction Graph mono
-- statement:
--   Shannon capacity is monotonic: if a/b ≤ c/d, then Θ(E_{a/b}) ≤ Θ(E_{c/d}).
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/FractionGraphs.lean#L886-L890
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/FractionGraphs.lean#L886-L890

import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_FractionGraphs
set_option autoImplicit true
open GroupTheoreticShannonCapacity
open Matrix

theorem GroupTheoreticShannonCapacity.shannonCapacity_fractionGraph_mono (a b c d : ℕ) [NeZero a] [NeZero c]
    (hb_pos : 0 < b) (hab_le_cd : (a : ℚ) / b ≤ (c : ℚ) / d) :
    shannonCapacity (fractionGraph a b) ≤ shannonCapacity (fractionGraph c d) := by sorry
