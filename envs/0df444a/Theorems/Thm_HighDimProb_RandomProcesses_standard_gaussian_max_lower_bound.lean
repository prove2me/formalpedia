-- Prove2me | Theorems.Thm_HighDimProb_RandomProcesses_standard_gaussian_max_lower_bound
-- name    : HighDimProb.RandomProcesses.standard_gaussian_max_lower_bound
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-02T11:05:46.042523+00:00
-- url     : https://prove2.me/theorems/2a25469d-dbd4-451d-9947-e0724237eed6
-- title:
--   Lower bound for the expected maximum of independent standard Gaussians
-- statement:
--   There exists an absolute constant c > 0 such that the expected maximum of any finite nonempty family of independent standard normal random variables is at least c sqrt(log n), where n is the number of variables. The variables are the coordinate projections under the product of standard Gaussian probability measures. This is the Gaussian maximum lower bound used in the proof of Sudakov minoration; the single-coordinate case has both sides zero.
-- source:
--   Vershynin, High-Dimensional Probability, first edition, Exercise 2.5.11 (Lower bound), printed p. 28 (PDF p. 36), invoked in the proof of Theorem 7.4.1 on printed p. 172 (PDF p. 180). https://www.math.uci.edu/~rvershyn/papers/HDP-book/HDP-1.pdf.

import Mathlib
open MeasureTheory ProbabilityTheory

theorem HighDimProb.RandomProcesses.standard_gaussian_max_lower_bound :
  ∃ c : ℝ, 0 < c ∧
    ∀ {ι : Type} [Fintype ι] [Nonempty ι],
      c * Real.sqrt (Real.log (Fintype.card ι)) ≤
        ∫ x : ι → ℝ, Finset.univ.sup' Finset.univ_nonempty x
          ∂Measure.pi (fun _ : ι => gaussianReal 0 1) := by sorry
