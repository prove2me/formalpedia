-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_independenceNumber_iso
-- name    : GroupTheoreticShannonCapacity.independenceNumber_iso
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T07:25:39.174387+00:00
-- url     : https://prove2.me/theorems/7c1c14ed-a9fc-4251-b7ef-69cbf43c78ec
-- title:
--   Group Theoretic Shannon Capacity: independence Number iso
-- statement:
--   Independence number is preserved under graph isomorphism.
--       This follows because isomorphisms bijectively map independent sets to independent sets.
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Basic.lean#L64-L67
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Basic.lean#L64-L67

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Clique
import Definitions.Def_GroupTheoreticShannonCapacity_Defs
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
set_option autoImplicit true
open GroupTheoreticShannonCapacity

theorem GroupTheoreticShannonCapacity.independenceNumber_iso {W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : G ≃g H) :
    G.indepNum = H.indepNum := by sorry
