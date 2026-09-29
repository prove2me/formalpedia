-- Prove2me | Theorems.Thm_Freiman_lowerEarlyTerminal_opposite_parity_cd
-- name    : Freiman.lowerEarlyTerminal_opposite_parity_cd
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:42:01.072579+00:00
-- url     : https://prove2.me/theorems/02d424ba-a6c7-4b2d-bd3b-91346aba16f6
-- title:
--   Freiman.lowerEarlyTerminal_opposite_parity_cd
-- statement:
--   Positive words beginning with a digit at least3 and with opposite length parity cannot have the same pair of denominator continuants. Opposite determinant signs would make the sum of their rational convergents an integer strictly between0 and1.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert. Report continuant determinant identity and the actual lower construction’s first-digit3/4 core restriction.

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry

open Freiman

theorem Freiman.lowerEarlyTerminal_opposite_parity_cd (u v : List ℕ+)
    (hu : ∃ a : ℕ+, ∃ w : List ℕ+, u = a::w ∧ 3 ≤ (a:ℕ))
    (hv : ∃ a : ℕ+, ∃ w : List ℕ+, v = a::w ∧ 3 ≤ (a:ℕ))
    (hp : u.length % 2 ≠ v.length % 2) : lowerCD u ≠ lowerCD v := by
  sorry
