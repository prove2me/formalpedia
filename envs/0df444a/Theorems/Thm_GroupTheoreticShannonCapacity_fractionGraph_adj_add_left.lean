-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_fractionGraph_adj_add_left
-- name    : GroupTheoreticShannonCapacity.fractionGraph_adj_add_left
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T07:27:41.882194+00:00
-- url     : https://prove2.me/theorems/3d5ab1da-399a-4f3f-b4df-efd1ca002e2a
-- title:
--   Group Theoretic Shannon Capacity: fraction Graph adj add left
-- statement:
--   Adjacency in fraction graph is translation invariant
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/FractionGraphs.lean#L488-L490
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/FractionGraphs.lean#L488-L490

import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_FractionGraphs
set_option autoImplicit true
open GroupTheoreticShannonCapacity
open Matrix

theorem GroupTheoreticShannonCapacity.fractionGraph_adj_add_left (p q : ℕ) [NeZero p] (c u v : ZMod p) :
    (fractionGraph p q).Adj (c + u) (c + v) ↔ (fractionGraph p q).Adj u v := by sorry
