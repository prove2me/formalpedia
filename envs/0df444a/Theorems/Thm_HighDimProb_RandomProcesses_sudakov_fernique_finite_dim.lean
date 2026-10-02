-- Prove2me | Theorems.Thm_HighDimProb_RandomProcesses_sudakov_fernique_finite_dim
-- name    : HighDimProb.RandomProcesses.sudakov_fernique_finite_dim
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-02T10:31:47.732563+00:00
-- url     : https://prove2.me/theorems/81bbd8be-9a0b-4848-ae75-a857831a486e
-- title:
--   Finite-dimensional Sudakov–Fernique comparison
-- statement:
--   Let X and Y be centered Gaussian vectors indexed by the same finite, nonempty set. If E[(X_i-X_j)^2] ≤ E[(Y_i-Y_j)^2] for every pair i,j, then E[max_i X_i] ≤ E[max_i Y_i]. No equality of coordinate variances is assumed. This is the finite comparison underlying the mission’s Sudakov–Fernique theorem for arbitrary index sets, whose processESup is defined through finite marginals.
-- source:
--   Vershynin, High-Dimensional Probability, first edition, Theorem 7.2.11 and Exercise 7.2.12, printed pp. 166–167 (PDF pp. 174–175). https://www.math.uci.edu/~rvershyn/papers/HDP-book/HDP-1.pdf. Finite-dimensional restriction of the stated Gaussian-process comparison.

import Mathlib
open MeasureTheory ProbabilityTheory

theorem HighDimProb.RandomProcesses.sudakov_fernique_finite_dim :
∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      {ι : Type} [Fintype ι] [Nonempty ι] (X Y : ι → Ω → ℝ)
      (hXG : IsGaussianProcess X P) (hYG : IsGaussianProcess Y P)
      (hXmean : ∀ i, ∫ ω, X i ω ∂P = 0) (hYmean : ∀ i, ∫ ω, Y i ω ∂P = 0)
      (hinc : ∀ i j, ∫ ω, (X i ω - X j ω) ^ 2 ∂P ≤ ∫ ω, (Y i ω - Y j ω) ^ 2 ∂P),
      ∫ ω, Finset.univ.sup' Finset.univ_nonempty (fun i => X i ω) ∂P ≤
        ∫ ω, Finset.univ.sup' Finset.univ_nonempty (fun i => Y i ω) ∂P := by sorry
