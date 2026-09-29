-- Prove2me | Theorems.Thm_Freiman_lower_late_route
-- name    : Freiman.lower_late_route
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:17:27.913406+00:00
-- url     : https://prove2.me/theorems/327196f3-4a7f-4dcf-bade-a57a33147053
-- title:
--   Freiman lower construction: late route
-- statement:
--   (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hd : ¬ lowerMixed p ∧ ¬ lowerA p 3 ∧ ¬ lowerA p 9 ∧ lowerL p ∧ ¬ lowerLStar p)
--       (he : lowerLateEntryDomain p) : ∃ ls : List LowerLabel, lowerLateRouteValid p ls
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_140_144.tex, complete incoming late domain

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_late_route (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hd : ¬ lowerMixed p ∧ ¬ lowerA p 3 ∧ ¬ lowerA p 9 ∧ lowerL p ∧ ¬ lowerLStar p)
    (he : lowerLateEntryDomain p) : ∃ ls : List LowerLabel, lowerLateRouteValid p ls := by
  sorry
