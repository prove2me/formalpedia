-- Prove2me | Theorems.Thm_Freiman_lower_initial_period_positive
-- name    : Freiman.lower_initial_period_positive
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:18:49.477275+00:00
-- url     : https://prove2.me/theorems/e6a994fb-690e-4b48-90b5-54d4dec74616
-- title:
--   Freiman lower construction: initial period positive
-- statement:
--   Positivity of the integer recurrence u0=0,u1=1,u(n+2)=86u(n+1)-u(n).
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, prop:lc-H-contacts; exact initial contact appendix

import Definitions.Def_Freiman_lowerInitialSeamData
import Definitions.Def_Freiman_lowerInitialNData
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

open scoped BigOperators

theorem Freiman.lower_initial_period_positive (n : ℕ) (hn : 0 < n) : 0 < lowerInitialU n := by
  sorry
