-- Prove2me | Theorems.Thm_LeastSquaresTD_Absorbing_lemma5_lstd_limit
-- name    : LeastSquaresTD.Absorbing.lemma5_lstd_limit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T02:02:38.399587+00:00
-- url     : https://prove2.me/theorems/16f27371-89a8-4023-9a8d-0434858a8209
-- title:
--   Lemma 5 — the LS TD limit under visit frequencies
-- statement:
--   Run the LS TD estimate $\theta_n$ from Equation (11) on an arbitrary finite Markov chain. Let $\pi_x$ be the limiting proportion of transitions departing state $x$. Assume almost surely that every state is visited infinitely often and those departure proportions converge to $\pi$. If $M=\Phi^\top\Pi(I-\gamma P)\Phi$ is invertible, then
--
--   $$
--   \theta_n\longrightarrow M^{-1}\Phi^\top\Pi\bar r\quad\text{almost surely}.
--   $$
--
--   This identifies the large-sample least-squares estimate with the matrix expression used in Theorem 1.
--
--   **Formalization Note** The paper writes $\theta_{\mathrm{LSTD}}$ for the limit; convergence is asserted directly here. The ordinary Markov path is specified by its initial distribution and finite-dimensional transition law. All observed transitions enter this estimator, as Equation (11) requires. Small-sample singular matrices use Lean's total inverse; the asserted limit includes eventual invertibility.
-- source:
--   Bradtke and Barto, Linear Least-Squares Algorithms for Temporal Difference Learning, Machine Learning 22 (1996), https://doi.org/10.1023/A:1018056104778, p. 43, Lemma 5; pp. 54–55, Proof of Lemma 5

import Definitions.Def_LeastSquaresTD_Absorbing_Estimator

namespace LeastSquaresTD.Absorbing

open MeasureTheory Filter Topology

variable {m : ℕ}

/-- Lemma 5, p. 43, for any finite Markov chain. The paper's `θ_LSTD` is
the limit of the estimates; `Tendsto` asserts that this limit exists.
Equation (11) uses every transition of this ordinary chain. -/
theorem lemma5_lstd_limit
    {X Ω : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    [MeasurableSpace X] [MeasurableSingletonClass X] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (C : Chain X) (S : X → ℝ) (R : X → X → ℝ)
    (φ : X → Fin m → ℝ) (γ : ℝ) (π : X → ℝ) (Z : ℕ → Ω → X)
    (hS_nonneg : ∀ x, 0 ≤ S x) (hS_sum : ∑ x, S x = 1)
    (hlaw : HasChainLaw C S μ Z)
    (hvisits : ∀ᵐ ω ∂μ, ∀ (x : X) (N : ℕ), ∃ n ≥ N, Z n ω = x)
    (hfreq : ∀ᵐ ω ∂μ, ∀ x,
      Tendsto (fun n => chainOutFrequency (fun k => Z k ω) x n) atTop (𝓝 (π x)))
    (hunit : IsUnit (limitMatrix C φ γ π)) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun n => chainLstdTheta R φ γ (fun k => Z k ω) n)
      atTop (𝓝 (Matrix.mulVec (limitMatrix C φ γ π)⁻¹
        (limitVector C R φ π))) := by sorry

end LeastSquaresTD.Absorbing
