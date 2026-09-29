-- Prove2me | Theorems.Thm_Freiman_lowerEarlyTerminal_width_tie_coefficients
-- name    : Freiman.lowerEarlyTerminal_width_tie_coefficients
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:41:56.07499+00:00
-- url     : https://prove2.me/theorems/9ccf398c-16fa-44e1-a7da-53fbf3f64c60
-- title:
--   Freiman.lowerEarlyTerminal_width_tie_coefficients
-- statement:
--   Equal full widths force equality of the rational and √21 coefficients of their denominator quadratics.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert. Full-width formula with α=(√21−3)/6, β=3α; irrationality of √21 separates the two integer coefficients.

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry

open Freiman

theorem Freiman.lowerEarlyTerminal_width_tie_coefficients (hw : ∀ w : List ℕ+, lowerWidth w = (lowerBeta-lowerAlpha)/
      ((((lowerCD w).1:ℝ)*lowerAlpha+(lowerCD w).2)*(((lowerCD w).1:ℝ)*lowerBeta+(lowerCD w).2))) (u v : List ℕ+)
    (h : lowerWidth u = lowerWidth v) : (((lowerCD u).1:ℤ)^2+((lowerCD u).2:ℤ)^2 =
        ((lowerCD v).1:ℤ)^2+((lowerCD v).2:ℤ)^2) ∧
      (4*((lowerCD u).1:ℤ)*(lowerCD u).2-3*((lowerCD u).1:ℤ)^2 =
        4*((lowerCD v).1:ℤ)*(lowerCD v).2-3*((lowerCD v).1:ℤ)^2) := by
  sorry
