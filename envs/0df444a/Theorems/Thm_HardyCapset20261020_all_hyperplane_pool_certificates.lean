-- Prove2me | Theorems.Thm_HardyCapset20261020_all_hyperplane_pool_certificates
-- name    : HardyCapset20261020.all_hyperplane_pool_certificates
-- status  : Open
-- author  : @Somehow
-- created : 2026-10-20T13:35:12.593096+00:00
-- url     : https://prove2.me/theorems/ec5d9e2d-645a-445c-ad49-e972f077bb7f
-- title:
--   Full-space rational certificate bound for every hyperplane
-- statement:
--   Let S be the exact input baseline, H any affine hyperplane with nonzero normal, and F=S outside H. For every B contained in the entire-space candidate pool of F for which F union B is a cap, there is a rational cost bounding the cardinality of B and strictly less than the number of deleted baseline points plus one. This is an OPEN Lean formalization target: the existing exact Python verifier checks 239 rational certificates and all 9840 hyperplanes via 246 orbits, but those computations are not yet Lean proofs. The formal conclusion supplies a rational cost witness; it does not assert an encoded certificate object or the global eight-dimensional cap-set bound.
-- source:
--   Private local manuscript: 八维 cap 的超平面补点定理 (2026-10-13), sections 2–5; exact input SHA256 fa12b2dc4918c38248b3039df101b5bb66ee85fd56c313389015c64979d7fb88. The conditional fixed-core theorem is not a global cap-set upper bound.

import Definitions.Def_HardyCapsetModel20261020
import Mathlib.Data.Rat.Cast.Order
set_option autoImplicit false

namespace HardyCapset20261020
theorem all_hyperplane_pool_certificates (n : Point) (hn : n ≠ 0)
    (t : ZMod 3) (B : Finset Point) (hB : B ⊆ pool (core n t))
    (hcap : IsCap (core n t ∪ B)) :
    ∃ cost : ℚ, (B.card : ℚ) ≤ cost ∧
      cost < ((baseline ∩ hyperplane n t).card : ℚ) + 1 := by sorry
end HardyCapset20261020
