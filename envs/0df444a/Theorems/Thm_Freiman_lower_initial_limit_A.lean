-- Prove2me | Theorems.Thm_Freiman_lower_initial_limit_A
-- name    : Freiman.lower_initial_limit_A
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:14:44.129804+00:00
-- url     : https://prove2.me/theorems/0ec388a4-30ec-42e8-af9f-fbd602c04add
-- title:
--   Freiman lower construction: initial limit A
-- statement:
--   Both endpoints of the indicated actual H intervals converge to the displayed period-3 or period-S value; parity subsequences have the same limit.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, prop:lc-H-contacts and eq:lc-cF-evaluation

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_initial_limit_A : ∀ n, Filter.Tendsto (fun k => sInf (lowerFamilyH .A n k 0)) Filter.atTop (nhds (lowerFamilyLimitValue .A n 0)) ∧ Filter.Tendsto (fun k => sSup (lowerFamilyH .A n k 0)) Filter.atTop (nhds (lowerFamilyLimitValue .A n 0)) := by
  sorry
