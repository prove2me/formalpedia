-- Prove2me | Theorems.Thm_Freiman_lower_initial_period_scaled_identity
-- name    : Freiman.lower_initial_period_scaled_identity
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:19:03.013985+00:00
-- url     : https://prove2.me/theorems/3941c6b5-5528-49b2-93ae-181d2c87fcc6
-- title:
--   Freiman lower construction: initial period scaled identity
-- statement:
--   Division by the positive recurrence scalar, preserving actual word matrices.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, prop:lc-H-contacts; exact initial contact appendix

import Definitions.Def_Freiman_lowerInitialSeamData
import Definitions.Def_Freiman_lowerInitialNData
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

open scoped BigOperators

theorem Freiman.lower_initial_period_scaled_identity (n : ℕ) (hn : 0 < n) (hp : 0 < lowerInitialU n)
    (hm : lowerInitialWordMatrix (lowerRepeat lowerPeriod n) =
    ⟨14*(lowerInitialU n:ℝ)-(lowerInitialU (n-1):ℝ),19*(lowerInitialU n:ℝ),
      53*(lowerInitialU n:ℝ),72*(lowerInitialU n:ℝ)-(lowerInitialU (n-1):ℝ)⟩) :
    lowerInitialWordMatrix (lowerRepeat lowerPeriod n) =
    lowerInitialMatScale (lowerInitialU n:ℝ) (lowerInitialP false (lowerInitialX n)) := by
  sorry
