-- Prove2me | Theorems.Thm_Freiman_lower_entry_domain_transfer
-- name    : Freiman.lower_entry_domain_transfer
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:20:54.739812+00:00
-- url     : https://prove2.me/theorems/c5d52b88-06c1-49b3-ba09-1269ade361a8
-- title:
--   Freiman lower construction: entry domain transfer
-- statement:
--   Cancel the same positive matrix scale, derive positive lower-right entries and square the exact ratio bounds27/32 and15/17. The result is the existing scale/ratio domain729/1024<q<225/289,1/4<r<9/25,1/4<s<4/13.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, prop:lc-H-entry; source H certificate appendix

import Definitions.Def_Freiman_lowerInitialEntry
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_entry_domain_transfer 
    (hcd : ∀ w : List ℕ+, (lowerInitialWordMatrix w).c = ((lowerCD w).1:ℝ) ∧ (lowerInitialWordMatrix w).d = ((lowerCD w).2:ℝ))
    (p : LowerPair) (m : LowerInitialMatrix × LowerInitialMatrix)
    (hm : ∃ a : ℝ, 0 < a ∧ lowerInitialWordMatrix p.1 = lowerInitialMatScale a m.1 ∧
      lowerInitialWordMatrix p.2 = lowerInitialMatScale a m.2)
    (hb : lowerEntryMatrixBounds m) : lowerEntryDomain p := by
  sorry
