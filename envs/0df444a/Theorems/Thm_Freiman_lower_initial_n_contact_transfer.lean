-- Prove2me | Theorems.Thm_Freiman_lower_initial_n_contact_transfer
-- name    : Freiman.lower_initial_n_contact_transfer
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:20:25.840541+00:00
-- url     : https://prove2.me/theorems/3b2ac120-88c4-4fb8-9f8d-cd78392a6766
-- title:
--   Freiman lower construction: initial n contact transfer
-- statement:
--   Cancel the common positive period scalar in all four actual prefixEval fractions, then clear their positive denominators. This connects the quartic to the unchanged n-word comparison.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, prop:lc-H-contacts; exact initial contact appendix

import Definitions.Def_Freiman_lowerInitialSeamData
import Definitions.Def_Freiman_lowerInitialNData
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

open scoped BigOperators

theorem Freiman.lower_initial_n_contact_transfer 
    (hp : ∀ n : ℕ, 0 < n → lowerInitialWordMatrix (lowerRepeat lowerPeriod n) =
      lowerInitialMatScale (lowerInitialU n:ℝ) (lowerInitialP false (lowerInitialX n)))
    (hw : ∀ (w : List ℕ+) (t : ℝ), 0 < t →
      prefixEval w t = lowerInitialMatEval (lowerInitialWordMatrix w) t ∧
      0 < lowerInitialMatDen (lowerInitialWordMatrix w) t ∧
      (lowerInitialWordMatrix w).a*(lowerInitialWordMatrix w).d -
      (lowerInitialWordMatrix w).b*(lowerInitialWordMatrix w).c = (-1:ℝ)^w.length)
    (c : LowerInitialNCase) (n : ℕ) (hn : 0 < n) (hu : 0 < lowerInitialU n)
    (hd : ∀ i : Fin 4, 0 < lowerInitialMatDen (lowerInitialNMatrix c i (lowerInitialX n)) lowerTau)
    (hpos : 0 < lowerInitialNNumerator c (lowerInitialX n)) : lowerInitialNHolds c n := by
  sorry
