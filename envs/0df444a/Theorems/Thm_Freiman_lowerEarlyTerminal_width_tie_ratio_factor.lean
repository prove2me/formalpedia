-- Prove2me | Theorems.Thm_Freiman_lowerEarlyTerminal_width_tie_ratio_factor
-- name    : Freiman.lowerEarlyTerminal_width_tie_ratio_factor
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:42:01.693912+00:00
-- url     : https://prove2.me/theorems/71c600fe-2448-454a-985e-392051304c6f
-- title:
--   Freiman.lowerEarlyTerminal_width_tie_ratio_factor
-- statement:
--   Factor the two equal integer quadratic invariants: denominator ratios either coincide or are related by the exact reflection (4−3r)/(3+4r).
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert.

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry

open Freiman

theorem Freiman.lowerEarlyTerminal_width_tie_ratio_factor (u v : List ℕ+) (h : (((lowerCD u).1:ℤ)^2+((lowerCD u).2:ℤ)^2 =
        ((lowerCD v).1:ℤ)^2+((lowerCD v).2:ℤ)^2) ∧
      (4*((lowerCD u).1:ℤ)*(lowerCD u).2-3*((lowerCD u).1:ℤ)^2 =
        4*((lowerCD v).1:ℤ)*(lowerCD v).2-3*((lowerCD v).1:ℤ)^2)) : lowerRatio u = lowerRatio v ∨
      lowerRatio v = (4-3*lowerRatio u)/(3+4*lowerRatio u) := by
  sorry
