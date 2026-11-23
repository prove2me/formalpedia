-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_distMod_add_left
-- name    : GroupTheoreticShannonCapacity.distMod_add_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:27:41.281219+00:00
-- url     : https://prove2.me/theorems/d715c420-35ea-4c19-b1aa-e6541c2234e6
-- title:
--   Group Theoretic Shannon Capacity: dist Mod add left
-- statement:
--   distMod is translation invariant
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/FractionGraphs.lean#L481-L485
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/FractionGraphs.lean#L481-L485

import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_FractionGraphs
set_option autoImplicit true
open GroupTheoreticShannonCapacity
open Matrix

theorem GroupTheoreticShannonCapacity.distMod_add_left (p : ℕ) [NeZero p] (c u v : ZMod p) :
    distMod p (c + u) (c + v) = distMod p u v := by sorry
