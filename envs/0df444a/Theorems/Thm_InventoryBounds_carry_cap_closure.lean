-- Prove2me | Theorems.Thm_InventoryBounds_carry_cap_closure
-- name    : InventoryBounds.carry_cap_closure
-- status  : Open
-- author  : @visuddhi
-- created : 2026-10-08T15:31:43.098978+00:00
-- url     : https://prove2.me/theorems/0fabf3aa-7042-4b5b-ba41-93018fca64d5
-- title:
--   Theorem 5.3 — one-period carry-safe cap closure
-- statement:
--   If current inventory and a base-stock threshold are at most a nonnegative cap a, demand is nonnegative, and the next cap b is at least a, the post-order level is at most a and next lost-sales inventory is at most b. Optimal-threshold containment is a separate theorem.
-- source:
--   Hanzhang Qin, David Simchi-Levi, Ruihao Zhu, Information Limits of Multistage Inventory Control: Learning, Valuation, and Censoring, arXiv:2609.37380v1 (29 September 2026), https://arxiv.org/abs/2609.37380v1, Theorem 5.3, proof

import Definitions.Def_InventoryBounds_Primitives
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace InventoryBounds

theorem carry_cap_closure (x s d a b : ℝ)
    (hx : x ≤ a) (hs : s ≤ a) (hd : 0 ≤ d)
    (ha : 0 ≤ a) (hab : a ≤ b) :
    max x s ≤ a ∧ lostNext (max x s) d ≤ b := by sorry

end InventoryBounds
