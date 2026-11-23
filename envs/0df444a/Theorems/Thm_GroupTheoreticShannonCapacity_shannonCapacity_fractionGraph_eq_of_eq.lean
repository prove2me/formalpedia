-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_shannonCapacity_fractionGraph_eq_of_eq
-- name    : GroupTheoreticShannonCapacity.shannonCapacity_fractionGraph_eq_of_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T07:28:00.786429+00:00
-- url     : https://prove2.me/theorems/8f46eede-ceb3-4c10-9b62-af249f858e38
-- title:
--   Group Theoretic Shannon Capacity: shannon Capacity fraction Graph eq of eq
-- statement:
--   Shannon capacity is equal for equivalent fractions: if a/b = c/d, then Θ(E_{a/b}) = Θ(E_{c/d}).
--   This follows from antisymmetry of monotonicity.
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/FractionGraphs.lean#L894-L899
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/FractionGraphs.lean#L894-L899

import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_FractionGraphs
set_option autoImplicit true
open GroupTheoreticShannonCapacity
open Matrix

theorem GroupTheoreticShannonCapacity.shannonCapacity_fractionGraph_eq_of_eq (a b c d : ℕ) [NeZero a] [NeZero c]
    (hb_pos : 0 < b) (hd_pos : 0 < d) (hab_eq_cd : (a : ℚ) / b = (c : ℚ) / d) :
    shannonCapacity (fractionGraph a b) = shannonCapacity (fractionGraph c d) := by sorry
