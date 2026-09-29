-- Prove2me | Theorems.Thm_Freiman_lower_initial_word_fraction
-- name    : Freiman.lower_initial_word_fraction
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:20:00.955344+00:00
-- url     : https://prove2.me/theorems/49aa2835-53ff-43bf-bcfa-d1cf6b1094a6
-- title:
--   Freiman lower construction: initial word fraction
-- statement:
--   Word induction connecting the source integer matrices, positive denominators, determinant parity and our existing prefixEval.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, prop:lc-H-contacts; exact initial contact appendix

import Definitions.Def_Freiman_lowerInitialSeamData
import Definitions.Def_Freiman_lowerInitialNData
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

open scoped BigOperators

theorem Freiman.lower_initial_word_fraction (w : List ℕ+) (t : ℝ) (ht : 0 < t) :
    prefixEval w t = lowerInitialMatEval (lowerInitialWordMatrix w) t ∧
    0 < lowerInitialMatDen (lowerInitialWordMatrix w) t ∧
    (lowerInitialWordMatrix w).a*(lowerInitialWordMatrix w).d -
    (lowerInitialWordMatrix w).b*(lowerInitialWordMatrix w).c = (-1:ℝ)^w.length := by
  sorry
