-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_fractionGraph_scalarMulMap_isCohom
-- name    : GroupTheoreticShannonCapacity.fractionGraph_scalarMulMap_isCohom
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T07:28:04.498872+00:00
-- url     : https://prove2.me/theorems/7ca54b24-91ea-4cf7-908b-8890f9a5f5aa
-- title:
--   Group Theoretic Shannon Capacity: fraction Graph scalar Mul Map is Cohom
-- statement:
--   The scalar multiplication map is a cohomomorphism when p' * q ≤ p * q'.
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/FractionGraphs.lean#L970-L1014
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/FractionGraphs.lean#L970-L1014

import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_FractionGraphs
set_option autoImplicit true
open GroupTheoreticShannonCapacity
open Matrix

theorem GroupTheoreticShannonCapacity.fractionGraph_scalarMulMap_isCohom (p' q' p q : ℕ) [NeZero p'] [NeZero (p' * p)]
    (hpq_ineq : p' * q ≤ p * q') :
    ∀ u v, u ≠ v → ¬(fractionGraph p' q').Adj u v →
      fractionGraph_scalarMulMap p' p u ≠ fractionGraph_scalarMulMap p' p v ∧
      ¬(fractionGraph (p' * p) (p' * q)).Adj
        (fractionGraph_scalarMulMap p' p u) (fractionGraph_scalarMulMap p' p v) := by sorry
