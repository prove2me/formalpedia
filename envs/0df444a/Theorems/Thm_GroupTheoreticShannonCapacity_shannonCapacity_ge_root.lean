-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_shannonCapacity_ge_root
-- name    : GroupTheoreticShannonCapacity.shannonCapacity_ge_root
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:26:15.605698+00:00
-- url     : https://prove2.me/theorems/dc86174c-bee9-40c4-a2ba-8be00bd3ba19
-- title:
--   Group Theoretic Shannon Capacity: shannon Capacity ge root
-- statement:
--   Lower bound: Shannon capacity is at least α(G^⊠n)^(1/n) for any n ≥ 1.
--   This follows directly from the definition of Shannon capacity as a supremum.
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Basic.lean#L214-L220
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Basic.lean#L214-L220

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Clique
import Definitions.Def_GroupTheoreticShannonCapacity_Defs
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
set_option autoImplicit true
open GroupTheoreticShannonCapacity

theorem GroupTheoreticShannonCapacity.shannonCapacity_ge_root (G : SimpleGraph V) [Fintype V] (n : ℕ) (hn : n ≥ 1) :
    shannonCapacity G ≥ ((strongPower G n).indepNum : ℝ) ^ (1 / (n : ℝ)) := by sorry
