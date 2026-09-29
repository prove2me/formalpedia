-- Prove2me | Theorems.Thm_Freiman_lower_path_growth
-- name    : Freiman.lower_path_growth
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:16:06.37299+00:00
-- url     : https://prove2.me/theorems/06df1f35-4256-4d33-a603-ecbc8874c1b4
-- title:
--   Freiman lower construction: path growth
-- statement:
--   (t : ℝ) (h : ℕ → LowerPair) (hh : lowerPath t h) :
--       Filter.Tendsto (fun n => (h n).1.length) Filter.atTop Filter.atTop ∧
--       Filter.Tendsto (fun n => (h n).2.length) Filter.atTop Filter.atTop
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, lem:lc-both-shrink

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_path_growth (t : ℝ) (h : ℕ → LowerPair) (hh : lowerPath t h) :
    Filter.Tendsto (fun n => (lowerPhysicalPath h n).1.length) Filter.atTop Filter.atTop ∧
    Filter.Tendsto (fun n => (lowerPhysicalPath h n).2.length) Filter.atTop Filter.atTop := by
  sorry
