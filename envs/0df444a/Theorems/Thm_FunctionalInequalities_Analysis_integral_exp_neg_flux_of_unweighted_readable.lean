-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_integral_exp_neg_flux_of_unweighted_readable
-- name    : FunctionalInequalities.Analysis.integral_exp_neg_flux_of_unweighted_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:06:02.59855+00:00
-- url     : https://prove2.me/theorems/ede33e09-7e75-4497-9ed6-66486b1825c1
-- title:
--   Exponential Weighting of an Unweighted Flux Identity
-- statement:
--   This is a weighted-testing lemma for compactly supported $C^1$ tests.
--
--   Let $u,c:\mathbb R^n\to\mathbb R$ be such that $u$ is $C^1$. Let $J_a$ be locally integrable for every coordinate $a$, and let $c$ be locally integrable. Assume that every compactly supported $C^1$ function $\phi$ satisfies
--
--   $$
--   \int\sum_aJ_a\,\partial_a\phi\,dx=-\int c\phi\,dx.
--   $$
--
--   Then $e^{-u}(c-\sum_aJ_a\partial_a u)$ is locally integrable, and every compactly supported $C^1$ function $\psi$ satisfies
--
--   $$
--   \int e^{-u}\sum_aJ_a\,\partial_a\psi\,dx
--   =-\int e^{-u}\left(c-\sum_aJ_a\partial_a u\right)\psi\,dx.
--   $$
--
--   The lemma is a product-rule interface for passing from an unweighted divergence identity to its $e^{-u}$-weighted form.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   private theorem integral_exp_neg_flux_of_unweighted {n : ℕ}
--       {u c : EuclideanSpace ℝ (Fin n) → ℝ}
--       {J : EuclideanSpace ℝ (Fin n) → Fin n → ℝ}
--       (hu : ContDiff ℝ 1 u)
--       (hJ : ∀ a : Fin n, LocallyIntegrable (fun x => J x a)
--         (volume : Measure (EuclideanSpace ℝ (Fin n))))
--       (hc : LocallyIntegrable c (volume : Measure (EuclideanSpace ℝ (Fin n))))
--       (hId : ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ,
--         ContDiff ℝ 1 φ → HasCompactSupport φ →
--         (∫ x, ∑ a : Fin n, J x a *
--           fderiv ℝ φ x (EuclideanSpace.basisFun (Fin n) ℝ a)
--           ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
--         -(∫ x, c x * φ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) :
--       LocallyIntegrable
--         (fun x => Real.exp (-u x) * (c x - ∑ a : Fin n, J x a *
--           fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ a)))
--         (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
--       ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
--         ContDiff ℝ 1 ψ → HasCompactSupport ψ →
--         (∫ x, Real.exp (-u x) * (∑ a : Fin n, J x a *
--           fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ a))
--           ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
--         -(∫ x, Real.exp (-u x) * (c x - ∑ a : Fin n, J x a *
--           fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ a)) * ψ x
--           ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/IntegrationByParts/WeakHessianEvolution`](https://prove2.me/theorems/d20d941d-a690-4ebe-9a63-a346adf8dd16).
--
--   Previous: [`ae_hessian_flux_forcing_minus_drift`](https://prove2.me/theorems/838d3785-b396-43ff-b452-a1eb6e64d796) · Next: [`integral_exp_neg_hessian_flux_eq_curvature_gram`](https://prove2.me/theorems/6d3ddc0c-45c1-4c79-b3d0-33799314293f).
--
--   [Source excerpt, lines 1285–1309](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/WeakHessianEvolution.lean#L1285-L1309) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/WeakHessianEvolution.lean#L1284-L1393 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.WeakHessianEvolution`, declaration `_private.FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.WeakHessianEvolution.0.FunctionalInequalities.Analysis.integral_exp_neg_flux_of_unweighted`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_WeakHessianEvolution

open Matrix MeasureTheory Set Filter

theorem FunctionalInequalities.Analysis.integral_exp_neg_flux_of_unweighted_readable {n : ℕ}
    {u c : EuclideanSpace ℝ (Fin n) → ℝ}
    {J : EuclideanSpace ℝ (Fin n) → Fin n → ℝ}
    (hu : ContDiff ℝ 1 u)
    (hJ : ∀ a : Fin n, LocallyIntegrable (fun x => J x a)
      (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hc : LocallyIntegrable c (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hId : ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ 1 φ → HasCompactSupport φ →
      (∫ x, ∑ a : Fin n, J x a *
        fderiv ℝ φ x (EuclideanSpace.basisFun (Fin n) ℝ a)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      -(∫ x, c x * φ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) :
    LocallyIntegrable
      (fun x => Real.exp (-u x) * (c x - ∑ a : Fin n, J x a *
        fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ a)))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      (∫ x, Real.exp (-u x) * (∑ a : Fin n, J x a *
        fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ a))
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      -(∫ x, Real.exp (-u x) * (c x - ∑ a : Fin n, J x a *
        fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ a)) * ψ x
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by sorry
