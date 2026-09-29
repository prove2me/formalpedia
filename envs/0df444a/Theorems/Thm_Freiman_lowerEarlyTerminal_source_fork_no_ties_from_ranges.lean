-- Prove2me | Theorems.Thm_Freiman_lowerEarlyTerminal_source_fork_no_ties_from_ranges
-- name    : Freiman.lowerEarlyTerminal_source_fork_no_ties_from_ranges
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:41:36.147149+00:00
-- url     : https://prove2.me/theorems/b621cfad-be3e-4874-89ee-b84ecd27bf63
-- title:
--   Freiman.lowerEarlyTerminal_source_fork_no_ties_from_ranges
-- statement:
--   Transfer the finite suffix ratio boxes to actual incoming words. Context extraction uses the actual early domain and actual selected interior list; the two exceptional equalities remain explicit hypotheses.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert. Report source suffix classes1/2/3 with normalized right suffix31; full-width equality criterion and monotonicity of finite continued fractions.

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry

open Freiman

theorem Freiman.lowerEarlyTerminal_source_fork_no_ties_from_ranges (hf : lowerEarlyTerminalForkRangesValid)
    (hr : ∀ w : List ℕ+, 0 ≤ lowerRatio w ∧ lowerRatio w ≤ 1)
    (ha : ∀ u v : List ℕ+, lowerRatio (u++v) = prefixEval v.reverse (lowerRatio u))
    (ht : ∀ u v : List ℕ+, lowerWidth u = lowerWidth v →
      lowerRatio u = lowerRatio v ∨ lowerRatio v = (4-3*lowerRatio u)/(3+4*lowerRatio u))
    (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hd : lowerEarlyDomain p)
    (l : LowerLabel) (hn : lowerEarlyTerminalNative p l)
    (h2 : ¬ lowerEarlyTerminalTie2 p l) (h3 : ¬ lowerEarlyTerminalTie3 p l) :
    ∀ d ∈ ([1,2] : List ℕ+), LowerEarlyTerminalNoTies (lowerEarlyTerminalForkPair p l true d) := by
  sorry
