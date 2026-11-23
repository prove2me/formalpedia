-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_shannonCapacity_iso
-- name    : GroupTheoreticShannonCapacity.shannonCapacity_iso
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:26:06.690965+00:00
-- url     : https://prove2.me/theorems/fb8772b8-52ca-428f-88be-949623f0cae0
-- title:
--   Group Theoretic Shannon Capacity: shannon Capacity iso
-- statement:
--   Shannon capacity is preserved under graph isomorphism.
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Basic.lean#L120-L127
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Basic.lean#L120-L127

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Clique
import Definitions.Def_GroupTheoreticShannonCapacity_Defs
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
set_option autoImplicit true
open GroupTheoreticShannonCapacity

theorem GroupTheoreticShannonCapacity.shannonCapacity_iso {W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : G ≃g H) :
    shannonCapacity G = shannonCapacity H := by sorry
