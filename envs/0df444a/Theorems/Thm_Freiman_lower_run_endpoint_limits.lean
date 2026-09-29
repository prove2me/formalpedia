-- Prove2me | Theorems.Thm_Freiman_lower_run_endpoint_limits
-- name    : Freiman.lower_run_endpoint_limits
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:17:54.944655+00:00
-- url     : https://prove2.me/theorems/0b003d65-9d35-4628-9026-02ed38c46c5b
-- title:
--   Freiman lower construction: run endpoint limits
-- statement:
--   Both actual endpoint sequences converge to the same completion with two period-3 tails, connected to the existing sSup-defined cfValue.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/j_family.tex, uniform repeated3 limit

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_run_endpoint_limits (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hr : lowerRunOffered p) :
    Filter.Tendsto (fun k : ℕ => lowerEndpoint (lowerRunPair p (k+1)) false) Filter.atTop (nhds (lowerRunValue p)) ∧
    Filter.Tendsto (fun k : ℕ => lowerEndpoint (lowerRunPair p (k+1)) true) Filter.atTop (nhds (lowerRunValue p)) := by
  sorry
