-- Prove2me | Theorems.Thm_Freiman_lower_cylinder_nonempty
-- name    : Freiman.lower_cylinder_nonempty
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:15:59.834618+00:00
-- url     : https://prove2.me/theorems/b3e279df-be3b-4014-9743-593c5c4d8933
-- title:
--   Freiman lower construction: cylinder nonempty
-- statement:
--   Complete both outward words by periodic 2; digit 2 resets every proper forbidden-word suffix and all core digits are at most 4.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, lem:lc-cylinders

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_cylinder_nonempty (p : LowerPair) (hp : lowerAdmissible p) :
    ∃ a : ℤ → ℕ+, LowerModel a ∧ lowerCylinder p a ∧ (∀ i : ℤ, (a i : ℕ) ≤ 4) := by
  sorry
