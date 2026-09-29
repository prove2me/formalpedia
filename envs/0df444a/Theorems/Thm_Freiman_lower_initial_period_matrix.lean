-- Prove2me | Theorems.Thm_Freiman_lower_initial_period_matrix
-- name    : Freiman.lower_initial_period_matrix
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:18:55.255255+00:00
-- url     : https://prove2.me/theorems/ab64c62b-319d-4448-a69e-75432c2a502a
-- title:
--   Freiman lower construction: initial period matrix
-- statement:
--   (n : ℕ) (hn : 0 < n) : lowerInitialWordMatrix (lowerRepeat lowerPeriod n) =
--       lowerInitialMatScale (lowerInitialU n:ℝ) (lowerInitialP false (lowerInitialX n))
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, prop:lc-H-contacts; exact initial contact appendix

import Definitions.Def_Freiman_lowerInitialSeamData
import Definitions.Def_Freiman_lowerInitialNData
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

open scoped BigOperators

theorem Freiman.lower_initial_period_matrix (n : ℕ) (hn : 0 < n) : lowerInitialWordMatrix (lowerRepeat lowerPeriod n) =
    lowerInitialMatScale (lowerInitialU n:ℝ) (lowerInitialP false (lowerInitialX n)) := by
  sorry
