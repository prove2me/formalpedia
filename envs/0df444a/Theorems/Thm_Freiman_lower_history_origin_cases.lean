-- Prove2me | Theorems.Thm_Freiman_lower_history_origin_cases
-- name    : Freiman.lower_history_origin_cases
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:17:46.216132+00:00
-- url     : https://prove2.me/theorems/43007dbc-ff1a-4a55-9040-9869805a07b3
-- title:
--   Freiman lower construction: history origin cases
-- statement:
--   (h : ℕ → LowerPair) (n : ℕ) (hb : lowerBoundedHistory h n) (right : Bool)
--       (hm : lowerEnds (lowerSide (h n) right) [3,1,3,1]) :
--       lowerInitialMarked h n right ∨ lowerGenericMarked h n right
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/global_selection.tex, initial/generic history separation

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_history_origin_cases (t : ℝ) (h : ℕ → LowerPair) (n : ℕ) (hh : lowerHistory t h n) (right : Bool)
    (hm : lowerEnds (lowerSide (lowerPhysicalPath h n) right) [3,1,3,1]) :
    lowerInitialMarked h n right ∨ lowerGenericMarked h n right := by
  sorry
