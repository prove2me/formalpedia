-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_cutoffCoefficients_admissible_readable
-- name    : FunctionalInequalities.KLS.BKL.Localization.cutoffCoefficients_admissible_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:08:53.332629+00:00
-- url     : https://prove2.me/theorems/b3c27db8-2231-4fb1-9cdc-cc4964163df3
-- title:
--   Admissibility of Cutoff Localization Coefficients
-- statement:
--   This statement formalizes the regularity and support properties of cutoff coefficients from Equation (67), p. 19, of Bizeul–Klartag–Lehec (arXiv:2610.05474v1).
--
--   Let $n\in\mathbb N$, let $\mu$ be a probability measure on `EuclideanSpace ℝ (Fin n)`, assume that its support is compact and that $\mu$ is isotropic, and let $\gamma$ be an admissible cutoff, expressed by `IsCutoff γ`. Then the cutoff drift and every cutoff noise column satisfy:
--
--   1. There is one $K\in[0,\infty)$ such that the cutoff drift and every cutoff noise column are globally $K$-Lipschitz.
--   2. There is one $B\in\mathbb R$ uniformly bounding the norms of the cutoff drift and all cutoff noise columns at every parameter.
--   3. The cutoff drift has compact support.
--   4. Every cutoff noise column has compact support.
--
--   Equivalently, the conclusion is the conjunction of the corresponding global Lipschitz, boundedness, and compact-support assertions. This is an admissibility result for the cutoff coefficients, not a statement about a stochastic process.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.BKL.Localization`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem cutoffCoefficients_admissible (hiso : KLS.Isotropic μ) {γ : Param n → ℝ} (hγ : IsCutoff γ) :
--       (∃ K : ℝ≥0, LipschitzWith K (cutoffDrift μ hc γ) ∧
--           ∀ k, LipschitzWith K fun p => cutoffNoise μ hc γ p k) ∧
--         (∃ B : ℝ, ∀ p, ‖cutoffDrift μ hc γ p‖ ≤ B ∧ ∀ k, ‖cutoffNoise μ hc γ p k‖ ≤ B) ∧
--         HasCompactSupport (cutoffDrift μ hc γ) ∧
--         ∀ k, HasCompactSupport fun p => cutoffNoise μ hc γ p k
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/Localization/Coefficients`](https://prove2.me/theorems/d4044301-d978-4415-85b5-191b3ecf6f74).
--
--   Definition modules: [`KLS/Isotropic`](https://prove2.me/theorems/b8da0fa3-d27f-46ae-b3b9-8c204df57e02).
--
--   Selected supporting theorems: [`Covariance.inner_operator_self_pos_of_affineSupport_eq_top`](https://prove2.me/theorems/5af59f78-fcb6-4c1e-a63a-8d36d8da7f37), [`locallyLipschitz_noise`](https://prove2.me/theorems/aa73acec-6bb4-4a4c-a7ca-0777d3c209ba), [`Isotropic.locallyLipschitz_inverseSqrt_covariance_joint`](https://prove2.me/theorems/315359b0-06f6-4b98-a4b9-2dc033ab5cf9), [`exists_lipschitzWith_smul_of_locallyLipschitz`](https://prove2.me/theorems/a69c5efc-cc10-4d88-8cc4-a8588fa667cb), [`contDiff_posteriorCovariance_joint`](https://prove2.me/theorems/a52d87ad-7224-4ad7-973f-f486c36649d8).
--
--   Previous: [`locallyLipschitz_noise`](https://prove2.me/theorems/aa73acec-6bb4-4a4c-a7ca-0777d3c209ba).
--
--   [Source excerpt, lines 153–158](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Localization/Coefficients.lean#L153-L158) · Frozen source `408915f`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Equation (67), p. 19 (unnumbered display) and the compact stage before it. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Localization/Coefficients.lean#L151-L173 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Localization.Coefficients`, declaration `FunctionalInequalities.KLS.BKL.Localization.cutoffCoefficients_admissible`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Coefficients

open scoped NNReal RealInnerProductSpace
variable {n : ℕ} (μ : MeasureTheory.ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).support)

theorem FunctionalInequalities.KLS.BKL.Localization.cutoffCoefficients_admissible_readable (hiso : KLS.Isotropic μ) {γ : Param n → ℝ} (hγ : IsCutoff γ) :
    (∃ K : ℝ≥0, LipschitzWith K (cutoffDrift μ hc γ) ∧
        ∀ k, LipschitzWith K fun p => cutoffNoise μ hc γ p k) ∧
      (∃ B : ℝ, ∀ p, ‖cutoffDrift μ hc γ p‖ ≤ B ∧ ∀ k, ‖cutoffNoise μ hc γ p k‖ ≤ B) ∧
      HasCompactSupport (cutoffDrift μ hc γ) ∧
      ∀ k, HasCompactSupport fun p => cutoffNoise μ hc γ p k := by sorry
