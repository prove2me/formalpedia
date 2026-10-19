-- Prove2me | Theorems.Thm_IntMul_Kappa_hist_moment_le_linear
-- name    : IntMul.Kappa.hist_moment_le_linear
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-16T21:27:06.740141+00:00
-- url     : https://prove2.me/theorems/f346e6ef-7391-4588-9049-b72b39da1cc9
-- title:
--   Affine majorant for finite network moment inequalities
-- statement:
--   For any finite histogram of natural-number widths and multiplicities, any natural width denominator m (including m=0), and 0≤a≤1, the network moment sum at exponent 1−a is at most the rational linear expression obtained by replacing each (w/m)^(1−a) with w/m+a. This provides exact rational upper bounds on the bit and complex network moments without evaluating real logarithms, and is valid independently of the integer-multiplication algorithm.
-- source:
--   Weighted arithmetic-geometric mean inequality, applied entrywise to the exact IntMul.Kappa.histMoment definition. Intended for the OpenAI integer multiplication proof and Jain round-six finite histograms; pinned Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib
import Definitions.Def_IntMul_KappaFramework

theorem IntMul.Kappa.hist_moment_le_linear (h : List (ℕ × ℕ)) (m : ℕ)
    (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    histMoment h m (1 - a) ≤
      (h.map fun p => (p.2 : ℝ) * ((p.1 : ℝ) / m + a)).sum := by sorry
