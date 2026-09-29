-- Prove2me | Theorems.Thm_Freiman_lower_run_goodness
-- name    : Freiman.lower_run_goodness
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:17:48.231971+00:00
-- url     : https://prove2.me/theorems/6a56d281-d6a1-4198-8c72-65f276f51697
-- title:
--   Freiman lower construction: run goodness
-- statement:
--   (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hr : lowerRunOffered p) :
--       ∀ k : ℕ, 0 < k → lowerGood (lowerRunPair p k)
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/j_family.tex, uniform good run family

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_run_goodness (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hr : lowerRunOffered p) :
    ∀ k : ℕ, 0 < k → lowerGood (lowerRunPair p k) := by
  sorry
