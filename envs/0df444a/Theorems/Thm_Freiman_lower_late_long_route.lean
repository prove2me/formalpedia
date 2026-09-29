-- Prove2me | Theorems.Thm_Freiman_lower_late_long_route
-- name    : Freiman.lower_late_long_route
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:17:24.157058+00:00
-- url     : https://prove2.me/theorems/5ebefaca-c8f8-4b2e-9bbd-2768acdf743f
-- title:
--   Freiman lower construction: late long route
-- statement:
--   Exhaustive finite path certificate among the 18 listed late candidates for the actual long-parent domain r≥13/17. It includes nonempty good intervals, two outer contacts, fresh endpoint normalization and safe words.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_140_144.tex, prop:late-cover

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_late_long_route (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hd : ¬ lowerMixed p ∧ ¬ lowerA p 3 ∧ ¬ lowerA p 9 ∧ lowerL p ∧ ¬ lowerLStar p)
    (hr : (13/17 : ℝ) ≤ lowerRatio (lowerNormalize p).1) : ∃ ls : List LowerLabel, lowerLateRouteValid p ls := by
  sorry
