-- Prove2me | Theorems.Thm_HardyCapset20261020_integer_rounding
-- name    : HardyCapset20261020.integer_rounding
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-20T13:32:27.379076+00:00
-- url     : https://prove2.me/theorems/69af14f9-2550-4fb6-b3c4-82be39e3b3bf
-- title:
--   Strict rational bound implies integer capacity
-- statement:
--   For natural numbers k and m and any rational cost, if k is at most that cost and the cost is strictly less than m+1, then k is at most m.
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
theorem integer_rounding (k m : ℕ) (cost : ℚ)
    (hk : (k : ℚ) ≤ cost) (hc : cost < (m : ℚ) + 1) : k ≤ m := by sorry
end HardyCapset20261020
