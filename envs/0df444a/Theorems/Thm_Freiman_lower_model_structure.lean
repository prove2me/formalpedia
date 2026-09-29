-- Prove2me | Theorems.Thm_Freiman_lower_model_structure
-- name    : Freiman.lower_model_structure
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:16:08.716233+00:00
-- url     : https://prove2.me/theorems/4c42fcc4-65ce-437d-b3b5-f559eb9e9a47
-- title:
--   Freiman lower construction: model structure
-- statement:
--   Finite inspection of the seven cores identifies every possible secondary 4 at coordinate +1 and proves the two forbidden 14/41 words and eventual three-digit background.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/foundations.tex, found:central-dominance; lower_core.tex, seven physical cores

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_model_structure (a : ℤ → ℕ+) (ha : LowerModel a) :
    (∀ i : ℤ, (a i : ℕ) ≤ 4) ∧ AvoidsBlock a [1,4] ∧ AvoidsBlock a [4,1] ∧
    EventuallyThree a ∧
    (∀ i : ℤ, i ≠ 0 → (a i : ℕ) = 4 → ∃ right : Bool,
      i = (if right then 1 else -1) ∧
      (lowerCylinder (if right then ([3,2,1],[4,3,1]) else ([4,3,1],[3,2,1])) a ∨
       lowerCylinder (if right then ([3,2,1,1,2],[4,3,2,2]) else ([4,3,2,2],[3,2,1,1,2])) a ∨
       lowerCylinder (if right then ([3,2,1,1,3],[4,3,2,3]) else ([4,3,2,3],[3,2,1,1,3])) a ∨
       lowerCylinder (if right then ([3,2,1,1,3],[4,3,2,2]) else ([4,3,2,2],[3,2,1,1,3])) a)) := by
  sorry
