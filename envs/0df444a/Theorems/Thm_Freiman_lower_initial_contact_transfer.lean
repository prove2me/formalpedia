-- Prove2me | Theorems.Thm_Freiman_lower_initial_contact_transfer
-- name    : Freiman.lower_initial_contact_transfer
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:19:57.10429+00:00
-- url     : https://prove2.me/theorems/717c5875-c0e8-4f9a-8e0b-065edf57c099
-- title:
--   Freiman lower construction: initial contact transfer
-- statement:
--   Clear positive denominators and the common positive scale. Multiplying by the actual first-word parity cancels both determinant signs, giving exactly lowerContact.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, prop:lc-H-contacts; exact initial contact appendix

import Definitions.Def_Freiman_lowerInitialSeamData
import Definitions.Def_Freiman_lowerInitialNData
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

open scoped BigOperators

theorem Freiman.lower_initial_contact_transfer 
    (hw : ∀ (w : List ℕ+) (t : ℝ), 0 < t →
      prefixEval w t = lowerInitialMatEval (lowerInitialWordMatrix w) t ∧
      0 < lowerInitialMatDen (lowerInitialWordMatrix w) t ∧
      (lowerInitialWordMatrix w).a*(lowerInitialWordMatrix w).d -
      (lowerInitialWordMatrix w).b*(lowerInitialWordMatrix w).c = (-1:ℝ)^w.length)
    (c : LowerInitialSeamCase) (n k p : ℕ) (hl : lowerInitialSeamLink c n k p)
    (hd : lowerInitialSeamDenPositive c (lowerInitialX n) (lowerInitialY k) (lowerInitialY p))
    (hn : 0 < lowerInitialSeamNumerator c (lowerInitialX n) (lowerInitialY k) (lowerInitialY p)) :
    lowerInitialSeamHolds c n k p := by
  sorry
