-- Prove2me | Theorems.Thm_Freiman_lower_initial_run_matrix
-- name    : Freiman.lower_initial_run_matrix
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:19:47.593206+00:00
-- url     : https://prove2.me/theorems/df31bc02-ba33-47a2-9630-3bc3bfbe3071
-- title:
--   Freiman lower construction: initial run matrix
-- statement:
--   Both actual run matrices, including the B-family preceding run k=0. The latter uses [[1-3y,y],[y,1]], not M3+yI.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, prop:lc-H-contacts; exact initial contact appendix

import Definitions.Def_Freiman_lowerInitialSeamData
import Definitions.Def_Freiman_lowerInitialNData
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

open scoped BigOperators

theorem Freiman.lower_initial_run_matrix (k : ℕ) :
    lowerInitialWordMatrix (List.replicate (k+1) (3:ℕ+)) =
      lowerInitialMatScale (lowerInitialV (k+1):ℝ) (lowerInitialK (lowerInitialY k)) ∧
    lowerInitialWordMatrix (List.replicate k (3:ℕ+)) =
      lowerInitialMatScale (lowerInitialV (k+1):ℝ) (lowerInitialKPrev (lowerInitialY k)) := by
  sorry
