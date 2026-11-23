-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_addSubgroupShannonCapacity_le_shannonCapacity
-- name    : GroupTheoreticShannonCapacity.addSubgroupShannonCapacity_le_shannonCapacity
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T07:25:36.070627+00:00
-- url     : https://prove2.me/theorems/c7698ec7-4f12-49ae-baf9-9344c7865b3f
-- title:
--   Group Theoretic Shannon Capacity: add Subgroup Shannon Capacity le shannon Capacity
-- statement:
--   Monotonicity: addSubgroupShannonCapacity ≤ shannonCapacity.
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Basic.lean#L263-L272
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Basic.lean#L263-L272

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Clique
import Definitions.Def_GroupTheoreticShannonCapacity_Defs
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
set_option autoImplicit true
open GroupTheoreticShannonCapacity

theorem GroupTheoreticShannonCapacity.addSubgroupShannonCapacity_le_shannonCapacity {G : Type*} [AddGroup G] [Fintype G]
    (Γ : SimpleGraph G) :
    addSubgroupShannonCapacity Γ ≤ shannonCapacity Γ := by sorry
