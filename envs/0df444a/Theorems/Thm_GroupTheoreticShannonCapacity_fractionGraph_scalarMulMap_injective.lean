-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_fractionGraph_scalarMulMap_injective
-- name    : GroupTheoreticShannonCapacity.fractionGraph_scalarMulMap_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:25:54.30193+00:00
-- url     : https://prove2.me/theorems/c34bc086-59af-422c-aecb-dbc553819400
-- title:
--   Group Theoretic Shannon Capacity: fraction Graph scalar Mul Map injective
-- statement:
--   The scalar multiplication map is injective.
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/FractionGraphs.lean#L952-L967
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/FractionGraphs.lean#L952-L967

import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_FractionGraphs
set_option autoImplicit true
open GroupTheoreticShannonCapacity
open Matrix

theorem GroupTheoreticShannonCapacity.fractionGraph_scalarMulMap_injective (p' p : ℕ) [NeZero p'] [NeZero (p' * p)] :
    Function.Injective (fractionGraph_scalarMulMap p' p) := by sorry
