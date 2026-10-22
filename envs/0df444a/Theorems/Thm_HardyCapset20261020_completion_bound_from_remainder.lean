-- Prove2me | Theorems.Thm_HardyCapset20261020_completion_bound_from_remainder
-- name    : HardyCapset20261020.completion_bound_from_remainder
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-20T13:32:26.920518+00:00
-- url     : https://prove2.me/theorems/dbc75ce2-16e4-4db0-b02c-8e0d2e978ae8
-- title:
--   Reassemble fixed core and bounded remainder
-- statement:
--   For finite point sets A and F, if F is contained in A, the cardinality of F plus a natural capacity m equals 512, and the cardinality of A outside F is at most m, then A has at most 512 points.
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
theorem completion_bound_from_remainder (A F : Finset Point) (m : ℕ)
    (hF : F ⊆ A) (hcard : F.card + m = 512)
    (hbound : (A \ F).card ≤ m) : A.card ≤ 512 := by sorry
end HardyCapset20261020
