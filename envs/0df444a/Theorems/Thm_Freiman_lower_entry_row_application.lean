-- Prove2me | Theorems.Thm_Freiman_lower_entry_row_application
-- name    : Freiman.lower_entry_row_application
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:21:29.989982+00:00
-- url     : https://prove2.me/theorems/1472ed80-5044-4593-bedb-fc1d077ab79c
-- title:
--   Freiman lower construction: entry row application
-- statement:
--   The exact two-prefix fractional-linear difference identity transfers a finite row to actual words with the existing ratios. It clears positive denominators and retains the actual equal parity.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, prop:lc-H-entry; source H certificate appendix

import Definitions.Def_Freiman_lowerInitialEntry
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_entry_row_application 
    (hfrac : ∀ (w : List ℕ+) (t : ℝ), 0 < t →
      prefixEval w t = lowerInitialMatEval (lowerInitialWordMatrix w) t ∧
      0 < lowerInitialMatDen (lowerInitialWordMatrix w) t ∧
      (lowerInitialWordMatrix w).a*(lowerInitialWordMatrix w).d -
      (lowerInitialWordMatrix w).b*(lowerInitialWordMatrix w).c = (-1:ℝ)^w.length)
    (hcd : ∀ w : List ℕ+, (lowerInitialWordMatrix w).c = ((lowerCD w).1:ℝ) ∧ (lowerInitialWordMatrix w).d = ((lowerCD w).2:ℝ))
    (p : LowerPair) (e : LowerEntryRow) (hd : lowerEntryDomain p)
    (hp : p.1.length % 2 = e.parity % 2 ∧ p.2.length % 2 = e.parity % 2)
    (he : lowerEntryRowValid e) :
    if e.strict then 0 < lowerEntryActualDifference p e else lowerEntryActualDifference p e = 0 := by
  sorry
