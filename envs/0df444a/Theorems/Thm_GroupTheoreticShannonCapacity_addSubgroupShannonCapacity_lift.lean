-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_addSubgroupShannonCapacity_lift
-- name    : GroupTheoreticShannonCapacity.addSubgroupShannonCapacity_lift
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T07:28:00.956806+00:00
-- url     : https://prove2.me/theorems/fea18289-ba24-4684-9940-8dc2f5119829
-- title:
--   Group Theoretic Shannon Capacity: add Subgroup Shannon Capacity lift
-- statement:
--   **Lemma 4.3**: Subgroup Shannon capacity lifts along fraction ordering.
--       If p'/q' ≤ p/q, there exist a,b with a/b = p/q such that
--       addSubgroupShannonCapacity(E_{a/b}) ≥ addSubgroupShannonCapacity(E_{p'/q'}).
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/FractionGraphs.lean#L1025-L1050
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/FractionGraphs.lean#L1025-L1050

import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_FractionGraphs
set_option autoImplicit true
open GroupTheoreticShannonCapacity
open Matrix

theorem GroupTheoreticShannonCapacity.addSubgroupShannonCapacity_lift {p' q' p q : ℕ} [NeZero p'] (hq' : 0 < q')
    (hp : p ≠ 0) (hq : 0 < q) (hle : (p' : ℚ) / q' ≤ (p : ℚ) / q) :
    ∃ (a b : ℕ) (_ : NeZero a) (_ : 0 < b), (a : ℚ) / b = (p : ℚ) / q ∧
      addSubgroupShannonCapacity (fractionGraph a b) ≥
        addSubgroupShannonCapacity (fractionGraph p' q') := by sorry
