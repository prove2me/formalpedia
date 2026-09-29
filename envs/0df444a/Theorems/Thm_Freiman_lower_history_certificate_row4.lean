-- Prove2me | Theorems.Thm_Freiman_lower_history_certificate_row4
-- name    : Freiman.lower_history_certificate_row4
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:17:34.01916+00:00
-- url     : https://prove2.me/theorems/9b1d6bcb-3493-4d71-8a5d-cab0f8ad370f
-- title:
--   Freiman lower construction: history certificate row4
-- statement:
--   Exact finite row-4 certificate implication on the proved seven-step history domain. Reconstruct inequalities from actual endpoint words; cover all suffix/width alternatives including ties; apply only previous-depth goodness and the carried-target priorities. Includes marked initial roots, whose catalogue is separate from generic births.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/global_selection.tex, lem:global-suffix-targets row 4; all-suffix-history certificate tables

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_history_certificate_row4 (t : ℝ) (h : ℕ → LowerPair) (n : ℕ) (hh : lowerHistory t h n)
    (hw : lowerBoundedHistory h n) :
    lowerMixed (h n) → ¬ lowerH (h n) 2 → ¬ lowerH (h n) 5 → ¬ lowerRStar (h n) := by
  sorry
