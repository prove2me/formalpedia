-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_shannonCapacity_bddAbove
-- name    : GroupTheoreticShannonCapacity.shannonCapacity_bddAbove
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T07:25:35.914045+00:00
-- url     : https://prove2.me/theorems/6a551a2d-bbb8-47ee-a102-416eba518ecc
-- title:
--   Group Theoretic Shannon Capacity: shannon Capacity bdd Above
-- statement:
--   The Shannon capacity sequence is bounded above by the cardinality of the vertex set.
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Basic.lean#L188-L210
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Basic.lean#L188-L210

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Clique
import Definitions.Def_GroupTheoreticShannonCapacity_Defs
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
set_option autoImplicit true
open GroupTheoreticShannonCapacity

theorem GroupTheoreticShannonCapacity.shannonCapacity_bddAbove (G : SimpleGraph V) [Fintype V] :
    BddAbove (Set.range fun m =>
      ((strongPower G (m + 1)).indepNum : ℝ) ^ (1 / (m + 1 : ℝ))) := by sorry
