-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_fractionGraph_cohomomorphism
-- name    : GroupTheoreticShannonCapacity.fractionGraph_cohomomorphism
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:27:41.839206+00:00
-- url     : https://prove2.me/theorems/8026b1fa-dad5-4ef0-8bc9-1bd69e0cb168
-- title:
--   Group Theoretic Shannon Capacity: fraction Graph cohomomorphism
-- statement:
--   The fraction graphs are ordered by cohomomorphism:
--       If a/b ≤ c/d, then there exists a cohomomorphism from E_{a/b} to E_{c/d}.
--       This is a corollary of `fractionGraph_scalingMap_isCohom`.
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/FractionGraphs.lean#L280-L284
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/FractionGraphs.lean#L280-L284

import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_FractionGraphs
set_option autoImplicit true
open GroupTheoreticShannonCapacity
open Matrix

theorem GroupTheoreticShannonCapacity.fractionGraph_cohomomorphism (a b c d : ℕ) [NeZero a] [NeZero c]
    (hb_pos : 0 < b) (hab_le_cd : (a : ℚ) / b ≤ (c : ℚ) / d) :
    ∃ f : ZMod a → ZMod c, ∀ u v, u ≠ v → ¬(fractionGraph a b).Adj u v →
      f u ≠ f v ∧ ¬(fractionGraph c d).Adj (f u) (f v) := by sorry
