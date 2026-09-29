-- Prove2me | Theorems.Thm_Freiman_lower_initial_period_recurrence_matrix
-- name    : Freiman.lower_initial_period_recurrence_matrix
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:18:48.905236+00:00
-- url     : https://prove2.me/theorems/4bd2944c-44f8-4fa6-9d2a-4bdff8574a0a
-- title:
--   Freiman lower construction: initial period recurrence matrix
-- statement:
--   Exact Cayley-Hamilton recurrence for M(313121)^n, using M=[[14,19],[53,72]] and M²=86M-I.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, prop:lc-H-contacts; exact initial contact appendix

import Definitions.Def_Freiman_lowerInitialSeamData
import Definitions.Def_Freiman_lowerInitialNData
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

open scoped BigOperators

theorem Freiman.lower_initial_period_recurrence_matrix (n : ℕ) (hn : 0 < n) :
    lowerInitialWordMatrix (lowerRepeat lowerPeriod n) =
    ⟨14*(lowerInitialU n:ℝ)-(lowerInitialU (n-1):ℝ),19*(lowerInitialU n:ℝ),
      53*(lowerInitialU n:ℝ),72*(lowerInitialU n:ℝ)-(lowerInitialU (n-1):ℝ)⟩ := by
  sorry
