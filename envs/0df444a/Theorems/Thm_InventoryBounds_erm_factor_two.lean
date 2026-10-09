-- Prove2me | Theorems.Thm_InventoryBounds_erm_factor_two
-- name    : InventoryBounds.erm_factor_two
-- status  : Open
-- author  : @visuddhi
-- created : 2026-10-08T15:31:57.588131+00:00
-- url     : https://prove2.me/theorems/4570789c-6c58-43bb-9db8-bc55fb8b0a72
-- title:
--   Lemma 4.2 — deterministic ERM regret transfer
-- statement:
--   If true and empirical real objectives differ by at most b at every candidate and the empirical value at the selected candidate is no larger than at a comparator, its true excess objective is at most 2b. No concentration event is proved here.
-- source:
--   Hanzhang Qin, David Simchi-Levi, Ruihao Zhu, Information Limits of Multistage Inventory Control: Learning, Valuation, and Censoring, arXiv:2609.37380v1 (29 September 2026), https://arxiv.org/abs/2609.37380v1, Lemma 4.2, final step

import Definitions.Def_InventoryBounds_Primitives
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace InventoryBounds

theorem erm_factor_two {α : Type*} (f fhat : α → ℝ)
    (s shat : α) (b : ℝ)
    (hdev : ∀ a, |f a - fhat a| ≤ b)
    (hemp : fhat shat ≤ fhat s) :
    f shat - f s ≤ 2 * b := by sorry

end InventoryBounds
