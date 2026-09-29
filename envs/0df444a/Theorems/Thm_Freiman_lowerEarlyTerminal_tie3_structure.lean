-- Prove2me | Theorems.Thm_Freiman_lowerEarlyTerminal_tie3_structure
-- name    : Freiman.lowerEarlyTerminal_tie3_structure
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:42:04.140645+00:00
-- url     : https://prove2.me/theorems/e90dfec4-5dfa-4932-a31c-0fe010ae7f37
-- title:
--   Freiman.lowerEarlyTerminal_tie3_structure
-- statement:
--   The exceptional left3 ordinary equality has equal C,D, opposite fork parity and first digits3/4. The reflected-ratio alternative is excluded by the explicit suffix ranges; equal ratios and equal quadratic invariants identify both positive denominator continuants.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert. Exact source pair U22,V322 with U ending3 and V ending31; ratio intervals [9/22,7/17] and [43/105,34/83], whose reflected ranges are disjoint. Actual lowerState supplies the seven base cores or their reflections.

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry

open Freiman

theorem Freiman.lowerEarlyTerminal_tie3_structure (hc : ∀ u v : List ℕ+, lowerWidth u = lowerWidth v → (((lowerCD u).1:ℤ)^2+((lowerCD u).2:ℤ)^2 =
        ((lowerCD v).1:ℤ)^2+((lowerCD v).2:ℤ)^2) ∧
      (4*((lowerCD u).1:ℤ)*(lowerCD u).2-3*((lowerCD u).1:ℤ)^2 =
        4*((lowerCD v).1:ℤ)*(lowerCD v).2-3*((lowerCD v).1:ℤ)^2))
    (ht : ∀ u v : List ℕ+, lowerWidth u = lowerWidth v →
      lowerRatio u = lowerRatio v ∨ lowerRatio v = (4-3*lowerRatio u)/(3+4*lowerRatio u))
    (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hd : lowerEarlyDomain p)
    (l : LowerLabel) (hn : lowerEarlyTerminalNative p l) (he : lowerEarlyTerminalTie3 p l) :
    let w := lowerEarlyTerminalForkPair p l true 2
    (∃ a : ℕ+, ∃ u : List ℕ+, w.1 = a::u ∧ 3 ≤ (a:ℕ)) ∧
    (∃ a : ℕ+, ∃ v : List ℕ+, w.2 = a::v ∧ 3 ≤ (a:ℕ)) ∧
    w.1.length % 2 ≠ w.2.length % 2 ∧ lowerCD w.1 = lowerCD w.2 := by
  sorry
