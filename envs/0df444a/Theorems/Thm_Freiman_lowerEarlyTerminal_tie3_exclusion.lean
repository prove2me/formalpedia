-- Prove2me | Theorems.Thm_Freiman_lowerEarlyTerminal_tie3_exclusion
-- name    : Freiman.lowerEarlyTerminal_tie3_exclusion
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:42:07.892452+00:00
-- url     : https://prove2.me/theorems/1908b5a6-380d-4406-9ffe-d3ccd3e494b3
-- title:
--   Freiman.lowerEarlyTerminal_tie3_exclusion
-- statement:
--   The remaining ordinary tie U22 versus V322 in the left3 class is impossible for actual admissible words: the disjoint reflected ranges force equal C,D, while opposite determinant signs and first digits3/4 make their convergent sum both an integer and strictly between0 and1.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert. Report seven initial cores and their reflections, continuant determinant identity; exceptional source label22/32, right fork digit2, ordinary width equality. This uses actual lowerState admissibility, not an unrestricted ratio box.

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry

open Freiman

theorem Freiman.lowerEarlyTerminal_tie3_exclusion (ht : ∀ u v : List ℕ+, lowerWidth u = lowerWidth v →
      lowerRatio u = lowerRatio v ∨ lowerRatio v = (4-3*lowerRatio u)/(3+4*lowerRatio u))
    (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hd : lowerEarlyDomain p)
    (l : LowerLabel) (hn : lowerEarlyTerminalNative p l) : ¬ lowerEarlyTerminalTie3 p l := by
  sorry
