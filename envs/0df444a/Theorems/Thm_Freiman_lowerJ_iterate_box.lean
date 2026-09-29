-- Prove2me | Theorems.Thm_Freiman_lowerJ_iterate_box
-- name    : Freiman.lowerJ_iterate_box
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:01:57.511703+00:00
-- url     : https://prove2.me/theorems/c309412a-c15d-4f2d-88c9-82c3fc3a83a7
-- title:
--   Freiman repeated-three proof: iterate box
-- statement:
--   The explicit scalar interval map φ([1/4,4/5])⊆[1/4,1/3] and invariant interval induction.
-- source:
--   Freiman report j_family.tex and j_certificates.tex, equal-three-width and lower-j3-uniform; exact source width-criterion route.

import Definitions.Def_Freiman_lowerJData
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FinCases

open Freiman

theorem Freiman.lowerJ_iterate_box (r : ℝ) (hr : r ∈ Set.Icc (1/4:ℝ) (4/5)) (k : ℕ) (hk : 0 < k) : (1/4:ℝ) ≤ lowerJIter k r ∧ lowerJIter k r ≤ (1/3:ℝ) := by
  sorry
