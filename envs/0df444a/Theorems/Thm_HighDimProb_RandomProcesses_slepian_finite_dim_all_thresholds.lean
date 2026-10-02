-- Prove2me | Theorems.Thm_HighDimProb_RandomProcesses_slepian_finite_dim_all_thresholds
-- name    : HighDimProb.RandomProcesses.slepian_finite_dim_all_thresholds
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-02T07:59:49.950262+00:00
-- url     : https://prove2.me/theorems/91b96c96-8ba1-4c07-9508-28676293789f
-- title:
--   Finite-dimensional Slepian for every real threshold
-- statement:
--   Let $X$ and $Y$ be centered Gaussian vectors indexed by the same finite, nonempty set. Suppose corresponding coordinates have equal second moments and $\mathbb E(X_i-X_j)^2\le\mathbb E(Y_i-Y_j)^2$ for every pair of coordinates. Then, for every real threshold $\tau$,
--
--   $$P\{\max_i X_i\ge\tau\}\le P\{\max_i Y_i\ge\tau\},\qquad
--   \mathbb E\max_i X_i\le\mathbb E\max_i Y_i.$$
--
--   This finite-dimensional version covers negative thresholds as well as nonnegative ones. It is exactly the common finite comparison needed by the mission's finite milestone and its general-index Slepian theorem, whose suprema are defined through finite marginals.
-- source:
--   Vershynin, High-Dimensional Probability, Theorem 7.2.1 and its finite-dimensional restriction, pp. 161–162; proof of Theorem 7.2.9, pp. 165–166 (PDF pp. 169–170 and 173–174). https://www.math.uci.edu/~rvershyn/papers/HDP-book/HDP-1.pdf. The finite theorem in the book is worded for nonnegative thresholds; the general theorem and the same smoothing argument cover all real thresholds.

import Mathlib
open MeasureTheory ProbabilityTheory

theorem HighDimProb.RandomProcesses.slepian_finite_dim_all_thresholds :
∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      {ι : Type} [Fintype ι] [Nonempty ι] (X Y : ι → Ω → ℝ)
      (hXG : IsGaussianProcess X P) (hYG : IsGaussianProcess Y P)
      (hXmean : ∀ i, ∫ ω, X i ω ∂P = 0) (hYmean : ∀ i, ∫ ω, Y i ω ∂P = 0)
      (hvar : ∀ i, ∫ ω, (X i ω) ^ 2 ∂P = ∫ ω, (Y i ω) ^ 2 ∂P)
      (hinc : ∀ i j, ∫ ω, (X i ω - X j ω) ^ 2 ∂P ≤ ∫ ω, (Y i ω - Y j ω) ^ 2 ∂P)
      (τ : ℝ),
      (P.real {ω | Finset.univ.sup' Finset.univ_nonempty (fun i => X i ω) ≥ τ} ≤
        P.real {ω | Finset.univ.sup' Finset.univ_nonempty (fun i => Y i ω) ≥ τ}) ∧
      ∫ ω, Finset.univ.sup' Finset.univ_nonempty (fun i => X i ω) ∂P ≤
        ∫ ω, Finset.univ.sup' Finset.univ_nonempty (fun i => Y i ω) ∂P := by sorry
