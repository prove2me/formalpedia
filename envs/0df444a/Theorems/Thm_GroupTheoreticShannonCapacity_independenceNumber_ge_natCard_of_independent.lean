-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_independenceNumber_ge_natCard_of_independent
-- name    : GroupTheoreticShannonCapacity.independenceNumber_ge_natCard_of_independent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:25:39.294466+00:00
-- url     : https://prove2.me/theorems/9ca4e7ec-570d-4c27-97e0-b60ccdf00cc5
-- title:
--   Group Theoretic Shannon Capacity: independence Number ge nat Card of independent
-- statement:
--   If S is an independent Set, then G.indepNum ≥ |S|.
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Basic.lean#L157-L173
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Basic.lean#L157-L173

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Clique
import Definitions.Def_GroupTheoreticShannonCapacity_Defs
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
set_option autoImplicit true
open GroupTheoreticShannonCapacity

theorem GroupTheoreticShannonCapacity.independenceNumber_ge_natCard_of_independent (G : SimpleGraph V) [Fintype V]
    (S : Set V) (hS : G.IsIndepSet S) :
    G.indepNum ≥ Nat.card S := by sorry
