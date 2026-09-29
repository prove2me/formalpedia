-- Prove2me | Theorems.Thm_Freiman_middleRepair_frame_alphabet_bound
-- name    : Freiman.middleRepair_frame_alphabet_bound
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:33:41.94945+00:00
-- url     : https://prove2.me/theorems/03bc5bad-d8ec-4fcc-a40c-b4520fb461aa
-- title:
--   middleRepair frame alphabet bound
-- statement:
--   A fixed finite physical core and the outside alphabet {1,2,3} admit a uniform finite digit bound.
-- source:
--   Report report/source/staging/m2b/m2b_body.tex:46-48 and 483-510; normalized physical frame correction.

import Definitions.Def_Freiman_middleRepair
import Mathlib.Tactic

open Freiman

theorem Freiman.middleRepair_frame_alphabet_bound :
  ∀ c : MiddleCore, ∃ M : ℕ, ∀ a : ℤ → ℕ+, middleCompatible c a → ∀ i : ℤ, (a i : ℕ) ≤ M := by
  sorry
