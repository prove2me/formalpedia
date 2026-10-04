-- Prove2me | Theorems.Thm_HighDimProb_RandomProcesses_sudakov_minoration_finite_separated
-- name    : HighDimProb.RandomProcesses.sudakov_minoration_finite_separated
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-02T11:01:47.243124+00:00
-- url     : https://prove2.me/theorems/68afc7e0-eec6-47fc-877b-ce31c007f190
-- title:
--   Sudakov minoration for a finite separated Gaussian family
-- statement:
--   There is an absolute constant c > 0 such that every centered Gaussian vector indexed by a finite nonempty set satisfies E[max_i X_i] ≥ c ε sqrt(log |I|), whenever ε ≥ 0 and E[(X_i-X_j)^2] ≥ ε² for every distinct pair i,j. This is the finite separated-family comparison step in the proof of Sudakov minoration. It follows by comparing to independent standard Gaussians scaled by ε/sqrt(2), using Sudakov–Fernique and the Gaussian maximum lower bound.
-- source:
--   Vershynin, High-Dimensional Probability, first edition, proof of Theorem 7.4.1, printed p. 172 (PDF p. 180), finite separated-family step. The independent Gaussian maximum bound invoked there is Exercise 2.5.11, printed p. 28 (PDF p. 36). https://www.math.uci.edu/~rvershyn/papers/HDP-book/HDP-1.pdf.

import Mathlib
open MeasureTheory ProbabilityTheory

theorem HighDimProb.RandomProcesses.sudakov_minoration_finite_separated :
∃ c : ℝ, 0 < c ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      {ι : Type} [Fintype ι] [Nonempty ι] (X : ι → Ω → ℝ)
      (hXG : IsGaussianProcess X P) (hXmean : ∀ i, ∫ ω, X i ω ∂P = 0)
      (ε : ℝ), 0 ≤ ε →
      (∀ i j, i ≠ j → ε ^ 2 ≤ ∫ ω, (X i ω - X j ω) ^ 2 ∂P) →
      c * ε * Real.sqrt (Real.log (Fintype.card ι)) ≤
        ∫ ω, Finset.univ.sup' Finset.univ_nonempty (fun i => X i ω) ∂P := by sorry
