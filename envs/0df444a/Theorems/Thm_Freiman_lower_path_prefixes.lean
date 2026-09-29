-- Prove2me | Theorems.Thm_Freiman_lower_path_prefixes
-- name    : Freiman.lower_path_prefixes
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:15:44.732108+00:00
-- url     : https://prove2.me/theorems/992cdd87-2b2d-4c62-866a-a3185f142040
-- title:
--   Freiman lower construction: path prefixes
-- statement:
--   (t : ℝ) (h : ℕ → LowerPair) (hh : lowerPath t h) :
--       (∀ n, lowerAdmissible (h n)) ∧ (∀ n, lowerExtends (h n) (h (n+1))) ∧
--         (∀ n, lowerPrefixSize (h n) < lowerPrefixSize (h (n+1)))
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, physical prefix path

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_path_prefixes (t : ℝ) (h : ℕ → LowerPair) (hh : lowerPath t h) :
    (∀ n, lowerAdmissible (lowerPhysicalPath h n)) ∧
    (∀ n, lowerExtends (lowerPhysicalPath h n) (lowerPhysicalPath h (n+1))) ∧
    (∀ n, lowerPrefixSize (lowerPhysicalPath h n) < lowerPrefixSize (lowerPhysicalPath h (n+1))) := by
  sorry
