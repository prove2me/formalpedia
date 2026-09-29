-- Prove2me | Theorems.Thm_Freiman_lower_initial_limit_period
-- name    : Freiman.lower_initial_limit_period
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:14:47.016981+00:00
-- url     : https://prove2.me/theorems/5d6be6a3-3064-4348-a673-594e5e3438dd
-- title:
--   Freiman lower construction: initial limit period
-- statement:
--   Both endpoints of the indicated actual H intervals converge to the displayed period-3 or period-S value; parity subsequences have the same limit.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, prop:lc-H-contacts and eq:lc-cF-evaluation

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_initial_limit_period : Filter.Tendsto (fun n => sInf (lowerFamilyH .A n 1 0)) Filter.atTop (nhds cF) ∧ Filter.Tendsto (fun n => sSup (lowerFamilyH .A n 1 0)) Filter.atTop (nhds cF) := by
  sorry
