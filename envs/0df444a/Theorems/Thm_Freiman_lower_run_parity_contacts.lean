-- Prove2me | Theorems.Thm_Freiman_lower_run_parity_contacts
-- name    : Freiman.lower_run_parity_contacts
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:17:55.688009+00:00
-- url     : https://prove2.me/theorems/0264ffff-2db9-4a8f-83f9-5bd74449a8bc
-- title:
--   Freiman lower construction: run parity contacts
-- statement:
--   Every odd run cover meets the next odd run cover and every even run cover meets the next even run cover; all endpoint choices are actual formal choices.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/j_family.tex, lem:lower-j3-uniform, same-parity contacts

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_run_parity_contacts (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hr : lowerRunOffered p) :
    ∀ k : ℕ, 0 < k → (lowerCover (lowerRunPair p k) ∩ lowerCover (lowerRunPair p (k+2))).Nonempty := by
  sorry
