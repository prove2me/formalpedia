-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_shannonCapacity_fractionGraph_le
-- name    : GroupTheoreticShannonCapacity.shannonCapacity_fractionGraph_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:25:52.398041+00:00
-- url     : https://prove2.me/theorems/73c5e127-38e0-4ac6-956b-4231f309468d
-- title:
--   Group Theoretic Shannon Capacity: shannon Capacity fraction Graph le
-- statement:
--   Upper bound: Shannon capacity of fraction graph is at most p/q.
--   This follows from the fractional clique covering argument.
--   Requires q ≤ p since otherwise p/q < 1 but Θ(E_{p/q}) = 1 (complete graph).
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/FractionGraphs.lean#L845-L883
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/FractionGraphs.lean#L845-L883

import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_FractionGraphs
set_option autoImplicit true
open GroupTheoreticShannonCapacity
open Matrix

theorem GroupTheoreticShannonCapacity.shannonCapacity_fractionGraph_le (p q : ℕ) [NeZero p] (hq : 0 < q) (hpq : q ≤ p) :
    shannonCapacity (fractionGraph p q) ≤ (p : ℝ) / q := by sorry
