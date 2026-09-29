-- Prove2me | Theorems.Thm_Freiman_lower_entry_aux_matrix
-- name    : Freiman.lower_entry_aux_matrix
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:20:57.719588+00:00
-- url     : https://prove2.me/theorems/6dbec282-f921-417a-a8db-aaea0e309691
-- title:
--   Freiman lower construction: entry aux matrix
-- statement:
--   Auxiliary B has period exponent n+1, no zero-period case and no run parameter. This identity is for the raw displayed words; actual normalization is proved separately from the parameter domain.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, prop:lc-H-entry; source H certificate appendix

import Definitions.Def_Freiman_lowerInitialEntry
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_entry_aux_matrix 
    (hp : ∀ n : ℕ, 0 < n → lowerInitialWordMatrix (lowerRepeat lowerPeriod n) =
      lowerInitialMatScale (lowerInitialU n:ℝ) (lowerInitialP false (lowerInitialX n)))
    (hu : ∀ n : ℕ, 0 < n → 0 < lowerInitialU n)
    (n k p : ℕ) :
    ∃ a : ℝ, 0 < a ∧
      lowerInitialWordMatrix (lowerFamilyPair .auxB n k p).1 =
        lowerInitialMatScale a (lowerEntryAuxMatrices (lowerInitialX (n+1))).1 ∧
      lowerInitialWordMatrix (lowerFamilyPair .auxB n k p).2 =
        lowerInitialMatScale a (lowerEntryAuxMatrices (lowerInitialX (n+1))).2 := by
  sorry
