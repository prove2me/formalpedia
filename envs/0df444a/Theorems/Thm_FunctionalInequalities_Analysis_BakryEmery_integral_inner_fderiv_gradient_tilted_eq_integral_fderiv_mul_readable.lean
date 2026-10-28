-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_integral_inner_fderiv_gradient_tilted_eq_integral_fderiv_mul_readable
-- name    : FunctionalInequalities.Analysis.BakryEmery.integral_inner_fderiv_gradient_tilted_eq_integral_fderiv_mul_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:34.838556+00:00
-- url     : https://prove2.me/theorems/6627935a-8ab5-4069-9ba3-e8134c1348f4
-- title:
--   Mean Hessian Identity for a Lipschitz Gradient
-- statement:
--   This formalizes the analytic part of Lemma 2.3 of Letwin (arXiv:2607.24164v1).
--
--   Let $E$ be a finite-dimensional real inner-product space and let $\phi:E\to\mathbb R$. Assume:
--
--   1. $\phi$ is $C^1$.
--   2. For some $G\in[0,\infty)$, the gradient $\nabla\phi$ is $G$-Lipschitz.
--   3. $\phi$ is convex on $E$.
--   4. $e^{-\phi}$ is integrable with respect to volume measure and
--      $$\int_E e^{-\phi(x)}\,dx=1.$$
--   5. The gradient belongs to $L^2(\nu)$, where $\nu=\operatorname{volume}.\operatorname{tilted}(-\phi)$.
--
--   Then, for all $u,v\in E$,
--   $$\int_E\left\langle D(\nabla\phi)(x)[u],v\right\rangle\,d\nu(x)=\int_E D\phi(x)[u]D\phi(x)[v] \,d\nu(x).$$
--
--   This identity relates the mean derivative of the Lipschitz gradient to products of directional derivatives and is useful in tilted integration-by-parts calculations.
--
--   **Formalization Note.** The derivative of $\nabla\phi$ is the pointwise Fréchet derivative supplied by `fderiv`; the equality is integrated against the normalized tilted measure.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.BakryEmery`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integral_inner_fderiv_gradient_tilted_eq_integral_fderiv_mul (φ : E → ℝ)
--       (hφ : ContDiff ℝ 1 φ) {G : NNReal} (hG : LipschitzWith G (gradient φ))
--       (hc : ConvexOn ℝ Set.univ φ)
--       (hexp : Integrable (fun x => Real.exp (-φ x)) (volume : Measure E))
--       (hnorm : ∫ x, Real.exp (-φ x) ∂(volume : Measure E) = 1)
--       (hgrad : MemLp (gradient φ) 2 ((volume : Measure E).tilted (-φ))) (u v : E) :
--       (∫ x, ⟪fderiv ℝ (gradient φ) x u, v⟫ ∂((volume : Measure E).tilted (-φ))) =
--         ∫ x, fderiv ℝ φ x u * fderiv ℝ φ x v ∂((volume : Measure E).tilted (-φ))
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/IntegrationByParts/LipschitzHessian`](https://prove2.me/theorems/a33bc411-81aa-4352-b34a-c6253ee0ed0a).
--
--   Supporting theorems: [`hasWeakDerivAlong_of_lipschitz`](https://prove2.me/theorems/b9fc0ec0-1bac-4138-9d6d-d21b20f114b9).
--
--   Next: [`integral_fderiv_tilted_eq_integral_mul_fderiv_of_bounded_lipschitz`](https://prove2.me/theorems/80255608-689e-4cd7-80cc-3b2a722fd329).
--
--   [Source excerpt, lines 30–37](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/LipschitzHessian.lean#L30-L37) · Frozen source `408915f`.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Lemma 2.3. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/LipschitzHessian.lean#L24-L224 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.LipschitzHessian`, declaration `FunctionalInequalities.Analysis.BakryEmery.integral_inner_fderiv_gradient_tilted_eq_integral_fderiv_mul`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_LipschitzHessian

open MeasureTheory Filter Topology
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
set_option maxHeartbeats 800000

theorem FunctionalInequalities.Analysis.BakryEmery.integral_inner_fderiv_gradient_tilted_eq_integral_fderiv_mul_readable (φ : E → ℝ)
    (hφ : ContDiff ℝ 1 φ) {G : NNReal} (hG : LipschitzWith G (gradient φ))
    (hc : ConvexOn ℝ Set.univ φ)
    (hexp : Integrable (fun x => Real.exp (-φ x)) (volume : Measure E))
    (hnorm : ∫ x, Real.exp (-φ x) ∂(volume : Measure E) = 1)
    (hgrad : MemLp (gradient φ) 2 ((volume : Measure E).tilted (-φ))) (u v : E) :
    (∫ x, ⟪fderiv ℝ (gradient φ) x u, v⟫ ∂((volume : Measure E).tilted (-φ))) =
      ∫ x, fderiv ℝ φ x u * fderiv ℝ φ x v ∂((volume : Measure E).tilted (-φ)) := by sorry
