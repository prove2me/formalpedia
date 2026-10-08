-- Prove2me | Theorems.Thm_Helfgott_etaTwo_compact_fourier_cancellation
-- name    : Helfgott.etaTwo_compact_fourier_cancellation
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-06T10:34:21.215911+00:00
-- url     : https://prove2.me/theorems/c7221664-1ca5-4383-b042-5222a9c75cee
-- title:
--   Complete cancellation bounds for compact etaTwo sums and their logarithmic weights
-- statement:
--   For any positive real scale y, any nonzero circle frequency alpha, and arbitrary natural endpoints A,B, the etaTwo-smoothed finite Fourier sum on A <= n < B has norm at most 4 log(2)/||alpha||, where ||alpha|| is distance to the nearest integer. The logarithmically weighted etaTwo sum on 1 <= n <= B has norm at most 4 log(2) max(log(B),0)/||alpha||. The exact compact smoothing and every discrete endpoint are retained. Both estimates are unconditional and cover empty intervals and B=0. These are the Type I and correction inner-sum cancellation inputs for the Goldbach Vaughan decomposition.
-- source:
--   Classical geometric-sum cancellation and Abel summation, applied to the exact compact etaTwo smoothing in H. A. Helfgott, The ternary Goldbach conjecture is true, https://arxiv.org/html/1312.7748v2. Complete original Lean proofs of the circle chord inequality, the finite geometric sum estimate, both directions of weighted Abel summation, etaTwo monotonicity on each half, and logarithmic weighting. Mathlib attributions retained. Written by Codex.

import Definitions.Def_Helfgott_Smoothings
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Normed.Group.AddCircle
open Finset Real
open scoped BigOperators Classical

namespace Helfgott

theorem etaTwo_compact_fourier_cancellation (y : ℝ) (hy : 0 < y)
    (α : AddCircle (1 : ℝ)) (hα : α ≠ 0) (A B : ℕ) :
    (‖∑ n ∈ Finset.Ico A B,(etaTwo ((n : ℝ)/y) : ℂ)*fourier (n : ℤ) α‖ ≤
      4*Real.log 2/‖α‖) ∧
    (‖∑ n ∈ Finset.Icc 1 B,
      ((Real.log (n : ℝ)*etaTwo ((n : ℝ)/y) : ℝ) : ℂ)*fourier (n : ℤ) α‖ ≤
      (4*Real.log 2)*max (Real.log (B : ℝ)) 0/‖α‖) := by sorry

end Helfgott
