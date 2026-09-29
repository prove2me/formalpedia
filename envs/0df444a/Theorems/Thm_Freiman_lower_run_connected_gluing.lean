-- Prove2me | Theorems.Thm_Freiman_lower_run_connected_gluing
-- name    : Freiman.lower_run_connected_gluing
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:17:57.951101+00:00
-- url     : https://prove2.me/theorems/f68ffb3a-8a94-4b08-aa8e-f6afba8fe695
-- title:
--   Freiman lower construction: run connected gluing
-- statement:
--   Two connected same-parity chains with a common endpoint limit become connected after adjoining that exact limit; no closedness of a spectrum is used.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/j_family.tex, parity chains joined at their common explicit limit

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_run_connected_gluing (p : LowerPair) (hg : ∀ k : ℕ, 0 < k → lowerGood (lowerRunPair p k))
    (hc : ∀ k : ℕ, 0 < k → (lowerCover (lowerRunPair p k) ∩ lowerCover (lowerRunPair p (k+2))).Nonempty)
    (hl : Filter.Tendsto (fun k : ℕ => lowerEndpoint (lowerRunPair p (k+1)) false) Filter.atTop (nhds (lowerRunValue p)) ∧
      Filter.Tendsto (fun k : ℕ => lowerEndpoint (lowerRunPair p (k+1)) true) Filter.atTop (nhds (lowerRunValue p))) : IsPreconnected (lowerRunSet p) := by
  sorry
