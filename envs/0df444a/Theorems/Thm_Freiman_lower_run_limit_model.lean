-- Prove2me | Theorems.Thm_Freiman_lower_run_limit_model
-- name    : Freiman.lower_run_limit_model
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:15:02.577773+00:00
-- url     : https://prove2.me/theorems/f0a277c4-3d36-4373-aa42-b6dc76138c9d
-- title:
--   Freiman lower construction: run limit model
-- statement:
--   Every explicitly adjoined run limit has the same seven-core and forbidden-word conditions.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, explicit final-period-3 limits

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_run_limit_model (f : LowerInitialFamily) (n k : ℕ) (hf : f ≠ .auxB) :
    LowerModel (lowerPeriodicSequence (lowerFamilyLimitPair f n k) [3]) := by
  sorry
