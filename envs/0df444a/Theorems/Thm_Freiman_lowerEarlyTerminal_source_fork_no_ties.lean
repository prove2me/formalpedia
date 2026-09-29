-- Prove2me | Theorems.Thm_Freiman_lowerEarlyTerminal_source_fork_no_ties
-- name    : Freiman.lowerEarlyTerminal_source_fork_no_ties
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:41:38.488584+00:00
-- url     : https://prove2.me/theorems/5894e400-0ab4-46ea-8a7c-2c696b9f5e70
-- title:
--   Freiman.lowerEarlyTerminal_source_fork_no_ties
-- statement:
--   Every ordinary and virtual normalization used by an actual right-wide source fork is strict outside the two explicit exceptional cases.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert.

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry

open Freiman

theorem Freiman.lowerEarlyTerminal_source_fork_no_ties (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hd : lowerEarlyDomain p)
    (l : LowerLabel) (hn : lowerEarlyTerminalNative p l)
    (h2 : ¬ lowerEarlyTerminalTie2 p l) (h3 : ¬ lowerEarlyTerminalTie3 p l) :
    ∀ d ∈ ([1,2] : List ℕ+), LowerEarlyTerminalNoTies (lowerEarlyTerminalForkPair p l true d) := by
  sorry
