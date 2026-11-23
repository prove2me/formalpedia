-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_isClique_arc
-- name    : GroupTheoreticShannonCapacity.isClique_arc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:27:56.096339+00:00
-- url     : https://prove2.me/theorems/4626d836-e7ac-4a67-a18a-8dfbd24c0cc8
-- title:
--   Group Theoretic Shannon Capacity: is Clique arc
-- statement:
--   Any translated arc {start, start+1, ..., start+(q-1)} is a clique in E_{p/q}.
--       Follows from isClique_range_fractionGraph by translation invariance.
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/FractionGraphs.lean#L554-L566
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/FractionGraphs.lean#L554-L566

import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_FractionGraphs
set_option autoImplicit true
open GroupTheoreticShannonCapacity
open Matrix

theorem GroupTheoreticShannonCapacity.isClique_arc (p q : ℕ) [NeZero p] (hq : 0 < q) (h2q : 2 * q ≤ p) (start : ZMod p) :
    (fractionGraph p q).IsClique ((Finset.range q).image (fun j : ℕ => start + j)) := by sorry
