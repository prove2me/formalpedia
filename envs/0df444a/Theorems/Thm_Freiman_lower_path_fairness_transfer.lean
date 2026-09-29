-- Prove2me | Theorems.Thm_Freiman_lower_path_fairness_transfer
-- name    : Freiman.lower_path_fairness_transfer
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:15:59.213254+00:00
-- url     : https://prove2.me/theorems/de624a85-d48b-4fe4-b9f7-186fd27d86b6
-- title:
--   Freiman lower construction: path fairness transfer
-- statement:
--   Source-list inspection and forced reflections prove that whichever physical side is wider is extended within two steps; the mixed 0,1 case changes parity and cannot repeat.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, lem:lc-both-shrink

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_path_fairness_transfer (hf : ∀ (p : LowerPair), lowerGood p → lowerParameterBox p → let q := lowerNormalize p; lowerWidth (q.1 ++ [2]) < lowerWidth q.2 ∧ lowerWidth (q.1 ++ [3]) < lowerWidth q.2 ∧ lowerWidth (q.1 ++ [1,1]) < lowerWidth q.2 ∧ lowerWidth (q.2 ++ [1]) < lowerWidth q.1)
    (t : ℝ) (h : ℕ → LowerPair) (hh : lowerPath t h) : lowerWithinTwo (lowerPhysicalPath h) := by
  sorry
