-- Prove2me | Theorems.Thm_FunctionalInequalities_Covariance_inner_operator_self_pos_of_affineSupport_eq_top_readable
-- name    : FunctionalInequalities.Covariance.inner_operator_self_pos_of_affineSupport_eq_top_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:06:26.356393+00:00
-- url     : https://prove2.me/theorems/5af59f78-fcb6-4c1e-a63a-8d36d8da7f37
-- title:
--   Strict Covariance Positivity from Full Affine Support
-- statement:
--   This proves strict positivity of the covariance operator under full affine support.
--
--   Let $E$ be a finite-dimensional real inner-product space with its Borel measurable structure, and let $\mu$ be a probability measure on $E$ such that $\operatorname{id}\in L^2(\mu)$. Assume that the affine support of $\mu$ is all of $E$:
--
--   $$
--   \operatorname{affineSupport}(\mu)=E.
--   $$
--
--   Then every nonzero vector $v\in E$ satisfies
--
--   $$
--   0<\langle \operatorname{Cov}(\mu)v,v\rangle.
--   $$
--
--   Thus the ambient covariance quadratic form is positive definite under the stated support condition.
--
--   The result is useful for obtaining invertibility or coercivity of covariance on a full affine support.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem Covariance.inner_operator_self_pos_of_affineSupport_eq_top (μ : ProbabilityMeasure E)
--       (h2 : MemLp id 2 (μ : Measure E)) (hfull : Probability.affineSupport μ = ⊤)
--       {v : E} (hv : v ≠ 0) : 0 < ⟪Covariance.operator (μ : Measure E) v, v⟫
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/Covariance/Positivity`](https://prove2.me/theorems/11f9423c-d823-4cf1-ba54-703b7213bca5).
--
--   Definition modules: [`Probability/Covariance/Basic`](https://prove2.me/theorems/c4e236b4-be51-468e-9de3-e2203fe87adc), [`Probability/AffineSupport`](https://prove2.me/theorems/94abfb4a-13e9-434c-bb03-f6b05ced8e81).
--
--   [Source excerpt, lines 21–23](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/Covariance/Positivity.lean#L21-L23) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Covariance/Positivity.lean#L20-L46 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Covariance.Positivity`, declaration `FunctionalInequalities.Covariance.inner_operator_self_pos_of_affineSupport_eq_top`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Covariance_Positivity

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.Covariance.inner_operator_self_pos_of_affineSupport_eq_top_readable (μ : ProbabilityMeasure E)
    (h2 : MemLp id 2 (μ : Measure E)) (hfull : Probability.affineSupport μ = ⊤)
    {v : E} (hv : v ≠ 0) : 0 < ⟪Covariance.operator (μ : Measure E) v, v⟫ := by sorry
