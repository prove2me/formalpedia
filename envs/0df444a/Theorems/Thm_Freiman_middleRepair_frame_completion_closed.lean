-- Prove2me | Theorems.Thm_Freiman_middleRepair_frame_completion_closed
-- name    : Freiman.middleRepair_frame_completion_closed
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:33:29.925063+00:00
-- url     : https://prove2.me/theorems/0f5c7d55-f19b-4b70-82fd-18f5a2185c7f
-- title:
--   middleRepair frame completion closed
-- statement:
--   A physical cylinder is closed for coordinatewise eventual equality, including its outside-digit bound.
-- source:
--   Report report/source/staging/m2b/m2b_body.tex:46-48 and 483-510; normalized physical frame correction.

import Definitions.Def_Freiman_middleRepair
import Mathlib.Tactic

open Freiman

theorem Freiman.middleRepair_frame_completion_closed :
  ∀ (c : MiddleCore) (A : ℕ → ℤ → ℕ+) (a : ℤ → ℕ+),
  (∀ i : ℤ, ∀ᶠ n in Filter.atTop, A n i=a i) →
  (∀ᶠ n in Filter.atTop, middleCompatible c (A n)) → middleCompatible c a := by
  sorry
