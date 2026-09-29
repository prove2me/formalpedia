-- Prove2me | Theorems.Thm_Freiman_lower_initial_limit_C
-- name    : Freiman.lower_initial_limit_C
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:14:54.195823+00:00
-- url     : https://prove2.me/theorems/44983719-d051-410d-893a-e4394c432ffd
-- title:
--   Freiman lower construction: initial limit C
-- statement:
--   Both endpoints of the indicated actual H intervals converge to the displayed period-3 or period-S value; parity subsequences have the same limit.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, prop:lc-H-contacts and eq:lc-cF-evaluation

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_initial_limit_C : ∀ n k, Filter.Tendsto (fun p => sInf (lowerFamilyH .C n k p)) Filter.atTop (nhds (lowerFamilyLimitValue .C n k)) ∧ Filter.Tendsto (fun p => sSup (lowerFamilyH .C n k p)) Filter.atTop (nhds (lowerFamilyLimitValue .C n k)) := by
  sorry
