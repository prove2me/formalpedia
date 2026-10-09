-- Prove2me | Theorems.Thm_InventoryBounds_one_step_exact_truncation
-- name    : InventoryBounds.one_step_exact_truncation
-- status  : Open
-- author  : @visuddhi
-- created : 2026-10-08T15:31:29.874973+00:00
-- url     : https://prove2.me/theorems/1dba54eb-bec4-4210-85ba-bd2f4f034a32
-- title:
--   Proposition 5.5 — pathwise one-period truncation identities
-- statement:
--   For any real holding and shortage coefficients and action y at or below a cap a, replacing d by min(d,a) preserves sales and leftover inventory. Original stage cost minus truncated stage cost equals p times the removed demand. This is the one-period algebraic component, not the full policy-gap theorem.
-- source:
--   Hanzhang Qin, David Simchi-Levi, Ruihao Zhu, Information Limits of Multistage Inventory Control: Learning, Valuation, and Censoring, arXiv:2609.37380v1 (29 September 2026), https://arxiv.org/abs/2609.37380v1, Proposition 5.5, proof

import Definitions.Def_InventoryBounds_Primitives
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace InventoryBounds

theorem one_step_exact_truncation (h p y d a : ℝ) (hya : y ≤ a) :
    sales y d = sales y (min d a) ∧
    lostNext y d = lostNext y (min d a) ∧
    stageCost h p y d - stageCost h p y (min d a) = p * (d - min d a) := by sorry

end InventoryBounds
