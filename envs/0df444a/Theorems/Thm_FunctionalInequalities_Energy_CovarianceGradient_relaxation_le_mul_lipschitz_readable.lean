-- Prove2me | Theorems.Thm_FunctionalInequalities_Energy_CovarianceGradient_relaxation_le_mul_lipschitz_readable
-- name    : FunctionalInequalities.Energy.CovarianceGradient.relaxation_le_mul_lipschitz_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:06:30.869163+00:00
-- url     : https://prove2.me/theorems/62ed0b65-a0a8-46f7-b7c9-4f855a09ceaf
-- title:
--   Covariance Relaxation Bound by Lipschitz Relaxation
-- statement:
--   This bounds the covariance relaxation by the covariance operator norm times the Lipschitz-gradient relaxation.
--
--   Let $V$ be a finite-dimensional complete real inner-product space with its Borel measurable structure, let $\nu$ be a probability measure, and let $m$ be an additive Haar measure. Assume that $\nu\ll m$ and that the frontier of the support of $\nu$ has $\nu$-measure zero. For any $f\in L^2(\nu)$ whose Lipschitz-gradient relaxation is finite,
--
--   $$
--   \operatorname{relaxation}_{\mathrm{Cov}}(\nu)(f)
--   \le
--   \left\|\operatorname{Cov}(\nu)\right\|_{+}\,
--   \operatorname{relaxation}_{\mathrm{Lip}}(\nu,m)(f).
--   $$
--
--   Here $\|\operatorname{Cov}(\nu)\|_{+}$ is the nonnegative norm value coerced to $[0,\infty]$.
--
--   This is an energy comparison, not an assertion that either relaxation is finite or that a Poincaré inequality holds.
--
--   **Formalization Note** The inequality is in `ENNReal`; the finiteness assumption is precisely that the Lipschitz relaxation is not top.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Energy.CovarianceGradient`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem relaxation_le_mul_lipschitz (hac : (ν : Measure V) ≪ m)
--       (hfr : (ν : Measure V) (frontier (ν : Measure V).support) = 0) (f : Lp ℝ 2 (ν : Measure V))
--       (hf : Energy.LipschitzGradient.relaxation ν m hac f ≠ ⊤) :
--       relaxation ν f ≤
--         (‖Covariance.operator (ν : Measure V)‖₊ : ENNReal) * Energy.LipschitzGradient.relaxation ν m hac f
--   ```
--
--   **Module navigation**
--
--   Module: [`Poincare/LipschitzGradient/Comparison`](https://prove2.me/theorems/2c2b9cea-02c3-4658-a545-11edfb033e0d).
--
--   Definition modules: [`Probability/Covariance/Basic`](https://prove2.me/theorems/c4e236b4-be51-468e-9de3-e2203fe87adc), [`Energy/Form/Functional`](https://prove2.me/theorems/4dfa9356-1019-4d47-ba3e-299615584765), [`Energy/CovarianceGradient/Basic`](https://prove2.me/theorems/517395bc-0a9a-4b82-b89c-ca3b5281db43).
--
--   Supporting theorems: [`relaxation_eq_ofLinearPMap`](https://prove2.me/theorems/ecd8db80-1079-4c3b-8976-dc3390ed944f), [`sequentialRelaxation_comp_le_mul`](https://prove2.me/theorems/6442fdfe-7a22-4ff2-a77c-0cf355fd2512), [`exists_norm_sq_eq_inner_of_isSymmetric`](https://prove2.me/theorems/9d757bbb-ea20-490b-bd49-9f4d92fbdf19).
--
--   Previous: [`constant_eq_lipschitz`](https://prove2.me/theorems/ad3e672a-6889-4720-aee1-47c1405b013e).
--
--   [Source excerpt, lines 211–215](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Poincare/LipschitzGradient/Comparison.lean#L211-L215) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Poincare/LipschitzGradient/Comparison.lean#L209-L246 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Poincare.LipschitzGradient.Comparison`, declaration `FunctionalInequalities.Energy.CovarianceGradient.relaxation_le_mul_lipschitz`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Poincare_LipschitzGradient_Comparison

open MeasureTheory Filter Topology
universe u
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
variable (ν : MeasureTheory.ProbabilityMeasure V) (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure]

theorem FunctionalInequalities.Energy.CovarianceGradient.relaxation_le_mul_lipschitz_readable (hac : (ν : Measure V) ≪ m)
    (hfr : (ν : Measure V) (frontier (ν : Measure V).support) = 0) (f : Lp ℝ 2 (ν : Measure V))
    (hf : Energy.LipschitzGradient.relaxation ν m hac f ≠ ⊤) :
    relaxation ν f ≤
      (‖Covariance.operator (ν : Measure V)‖₊ : ENNReal) * Energy.LipschitzGradient.relaxation ν m hac f := by sorry
