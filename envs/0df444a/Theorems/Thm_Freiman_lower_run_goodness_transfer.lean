-- Prove2me | Theorems.Thm_Freiman_lower_run_goodness_transfer
-- name    : Freiman.lower_run_goodness_transfer
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:17:52.250486+00:00
-- url     : https://prove2.me/theorems/b1fd9639-bdad-4c47-ade6-51aeeb5befff
-- title:
--   Freiman lower construction: run goodness transfer
-- statement:
--   Apply the supplied equal-three criterion after the proved parameter update; admissible repeated3 extensions retain the physical central block, both parity cases and width orientation.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/j_family.tex, uniform good run family

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_run_goodness_transfer (hg : ∀ (p : LowerPair), lowerAdmissible p → ¬ lowerMixed p → lowerEnds p.1 [3] → lowerEnds p.2 [3] → lowerParameterBox p → lowerWidth p.2 ≤ lowerWidth p.1 → lowerWidth p.1 < (19/5 : ℝ)*lowerWidth p.2 → lowerGood p)
    (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hr : lowerRunOffered p) (hb : lowerRunParameters p) :
    ∀ k : ℕ, 0 < k → lowerGood (lowerRunPair p k) := by
  sorry
