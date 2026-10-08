-- Prove2me | Theorems.Thm_Helfgott_LFunction_local_zero_count_linear
-- name    : Helfgott.LFunction_local_zero_count_linear
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-05T14:35:09.461824+00:00
-- url     : https://prove2.me/theorems/149c5139-591b-473e-b732-571953531607
-- title:
--   Full multiplicity-weighted local Dirichlet L-function zero count linear in height
-- statement:
--   For every Dirichlet character of positive modulus, there is a finite nonnegative constant K such that, for every T>=8, the sum of actual analytic zero multiplicities in the closed disk of radius four centered at 2+iT is at most K(1+T). The proof derives every L-function strip-growth and anchor input in full, then uses Jensen on the larger disk of radius five. Principal characters are included, and their pole lies outside every disk used. No zero-count, gamma-growth or nonzero anchor estimate is assumed. This enables quantitative zero-avoiding contour heights; final logarithmic derivative and Goldbach numerical residual estimates remain separate.
-- source:
--   Helfgott, Major arcs for Goldbach’s problem, https://arxiv.org/abs/1305.2897. Mathlib Jensen formula/divisors and complex analysis by Stefan Kebekus and contributors; L-function/Mellin functional-equation contributors including David Loeffler; gamma, reflection, Euler inverse and sum-integral contributors. Complete original actual L-function growth and Jensen application. Written by Codex.

import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Analysis.Complex.JensenFormula
open Complex Metric Set Filter MeromorphicOn
open scoped Topology

theorem Helfgott.LFunction_local_zero_count_linear (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) :
    ∃ K : ℝ,0 ≤ K ∧ ∀ T : ℝ,8 ≤ T →
      ((∑ᶠ z : ℂ,divisor χ.LFunction (closedBall ((2 : ℂ)+(T : ℂ)*I) 4) z : ℤ) : ℝ) ≤ K*(1+T) := by sorry
