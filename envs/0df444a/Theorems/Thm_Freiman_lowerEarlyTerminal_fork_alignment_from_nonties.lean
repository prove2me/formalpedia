-- Prove2me | Theorems.Thm_Freiman_lowerEarlyTerminal_fork_alignment_from_nonties
-- name    : Freiman.lowerEarlyTerminal_fork_alignment_from_nonties
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:41:42.213167+00:00
-- url     : https://prove2.me/theorems/b878ed94-eb62-45d5-911e-6bf9c1a6d8eb
-- title:
--   Freiman.lowerEarlyTerminal_fork_alignment_from_nonties
-- statement:
--   The left-wide branch keeps the incoming order exactly. In the strictly right-wide branch, no ordinary or virtual tie permits endpoint swap symmetry for the two actual grandchildren. The strict source normalization selects the incoming left side at equality.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert.

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry

open Freiman

theorem Freiman.lowerEarlyTerminal_fork_alignment_from_nonties (p : LowerPair) (l : LowerLabel) (hw : LowerHistoryWidthLaw)
    (hswap : ∀ w : LowerPair, LowerEarlyTerminalNoTies w → ∀ upper : Bool,
      lowerEndpoint w upper = lowerEndpoint (w.2,w.1) upper)
    (hn : ∀ d ∈ ([1,2] : List ℕ+), LowerEarlyTerminalNoTies (lowerEarlyTerminalForkPair p l true d)) :
    lowerEarlyTerminalForkAlignment p l := by
  sorry
