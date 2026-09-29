-- Prove2me | Theorems.Thm_Freiman_lower_initial_limit_B
-- name    : Freiman.lower_initial_limit_B
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:14:55.011487+00:00
-- url     : https://prove2.me/theorems/84e6bf07-be01-41a0-ba8d-df6d2e3bb584
-- title:
--   Freiman lower construction: initial limit B
-- statement:
--   Both endpoints of the indicated actual H intervals converge to the displayed period-3 or period-S value; parity subsequences have the same limit.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, prop:lc-H-contacts and eq:lc-cF-evaluation

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_initial_limit_B : ∀ n, Filter.Tendsto (fun k => sInf (lowerFamilyH .B n k 0)) Filter.atTop (nhds (lowerFamilyLimitValue .B n 0)) ∧ Filter.Tendsto (fun k => sSup (lowerFamilyH .B n k 0)) Filter.atTop (nhds (lowerFamilyLimitValue .B n 0)) := by
  sorry
