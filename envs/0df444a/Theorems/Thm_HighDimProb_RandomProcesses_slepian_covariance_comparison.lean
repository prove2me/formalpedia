-- Prove2me | Theorems.Thm_HighDimProb_RandomProcesses_slepian_covariance_comparison
-- name    : HighDimProb.RandomProcesses.slepian_covariance_comparison
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-02T07:59:48.554344+00:00
-- url     : https://prove2.me/theorems/bea1b695-e45b-41d4-acb8-972f69eab14f
-- title:
--   Slepian moment assumptions order the covariance matrices
-- statement:
--   Let $(X_t)_{t\in T}$ and $(Y_t)_{t\in T}$ be centered real Gaussian processes on a probability space. Suppose
--
--   $$\mathbb E X_t^2=\mathbb E Y_t^2,\qquad
--   \mathbb E(X_t-X_s)^2\le\mathbb E(Y_t-Y_s)^2$$
--
--   for every $t,s\in T$. Then their covariance matrices have equal diagonal entries, and
--
--   $$\operatorname{Cov}(Y_t,Y_s)\le\operatorname{Cov}(X_t,X_s)$$
--
--   for every $t,s\in T$. This is the covariance ordering that determines the sign of the derivative in Slepian's Gaussian interpolation argument. The result does not require the index set to be finite.
-- source:
--   Vershynin, High-Dimensional Probability (first edition), Proof of Lemma 7.2.8, p. 165 (PDF p. 173). https://www.math.uci.edu/~rvershyn/papers/HDP-book/HDP-1.pdf. Explicit regularity and integrability hypotheses specify the analytic form used here.

import Mathlib
open MeasureTheory ProbabilityTheory Filter

theorem HighDimProb.RandomProcesses.slepian_covariance_comparison {Ω T : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : T → Ω → ℝ)
    (hXG : IsGaussianProcess X P) (hYG : IsGaussianProcess Y P)
    (hXmean : ∀ i, ∫ ω, X i ω ∂P = 0) (hYmean : ∀ i, ∫ ω, Y i ω ∂P = 0)
    (hvar : ∀ i, ∫ ω, (X i ω) ^ 2 ∂P = ∫ ω, (Y i ω) ^ 2 ∂P)
    (hinc : ∀ i j, ∫ ω, (X i ω - X j ω) ^ 2 ∂P ≤
      ∫ ω, (Y i ω - Y j ω) ^ 2 ∂P) :
    (∀ i, cov[X i, X i; P] = cov[Y i, Y i; P]) ∧
      ∀ i j, cov[Y i, Y j; P] ≤ cov[X i, X j; P] := by sorry
