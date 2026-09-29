-- Prove2me | Theorems.Thm_Freiman_lower_path_fairness
-- name    : Freiman.lower_path_fairness
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:15:47.56999+00:00
-- url     : https://prove2.me/theorems/9c3727c3-936f-4542-b605-2bc58ea59971
-- title:
--   Freiman lower construction: path fairness
-- statement:
--   (t : ℝ) (h : ℕ → LowerPair) (hh : lowerPath t h) : lowerWithinTwo h
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, lem:lc-both-shrink

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_path_fairness (t : ℝ) (h : ℕ → LowerPair) (hh : lowerPath t h) : lowerWithinTwo (lowerPhysicalPath h) := by
  sorry
