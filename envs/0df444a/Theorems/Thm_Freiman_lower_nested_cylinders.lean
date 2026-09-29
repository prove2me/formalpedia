-- Prove2me | Theorems.Thm_Freiman_lower_nested_cylinders
-- name    : Freiman.lower_nested_cylinders
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:15:57.633975+00:00
-- url     : https://prove2.me/theorems/4ebdf911-f785-4a16-8dc3-6d43973aae8b
-- title:
--   Freiman lower construction: nested cylinders
-- statement:
--   (h : ℕ → LowerPair) (ha : ∀ n, lowerAdmissible (h n))
--       (he : ∀ n, lowerExtends (h n) (h (n+1))) :
--       ∃ a : ℤ → ℕ+, LowerModel a ∧ ∀ n, lowerCylinder (h n) a
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, lem:lc-cylinders

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_nested_cylinders (h : ℕ → LowerPair) (ha : ∀ n, lowerAdmissible (h n))
    (he : ∀ n, lowerExtends (h n) (h (n+1))) :
    ∃ a : ℤ → ℕ+, LowerModel a ∧ ∀ n, lowerCylinder (h n) a := by
  sorry
