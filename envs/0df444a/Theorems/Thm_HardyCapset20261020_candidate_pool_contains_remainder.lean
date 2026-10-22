-- Prove2me | Theorems.Thm_HardyCapset20261020_candidate_pool_contains_remainder
-- name    : HardyCapset20261020.candidate_pool_contains_remainder
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-20T13:32:27.921674+00:00
-- url     : https://prove2.me/theorems/a6f2bdff-8146-46e6-896f-747075719a04
-- title:
--   Candidate-pool completeness for any fixed core
-- statement:
--   For any finite cap A in the eight-dimensional space over the field with three elements and any subset F of A, every member of A outside F belongs to the full-space candidate pool of F. Thus the pool excludes no feasible added point.
-- source:
--   Private local manuscript: 八维 cap 的超平面补点定理 (2026-10-13), sections 2–5; exact input SHA256 fa12b2dc4918c38248b3039df101b5bb66ee85fd56c313389015c64979d7fb88. The conditional fixed-core theorem is not a global cap-set upper bound.

import Definitions.Def_HardyCapsetModel20261020
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum

open scoped BigOperators
set_option maxRecDepth 4096
set_option autoImplicit false

namespace HardyCapset20261020
theorem candidate_pool_contains_remainder (A F : Finset Point)
    (hA : IsCap A) (hF : F ⊆ A) : A \ F ⊆ pool F := by sorry
end HardyCapset20261020
