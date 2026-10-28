-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_integral_mul_generator_eq_neg_energy_prime_readable
-- name    : FunctionalInequalities.Analysis.integral_mul_generator_eq_neg_energy_prime_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:32.42141+00:00
-- url     : https://prove2.me/theorems/12ffe5ab-1e01-479f-819d-012727f89a87
-- title:
--   Swapped Weak Generator Integration Identity
-- statement:
--   This formalizes the weak inverse-Hessian generator identity with the roles of the test functions exchanged.
--
--   Let $u,V,w,\eta:\mathbb R^n\to\mathbb R$. Assume: (1) $u,w\in C^1$, $\eta\in C^2$, and $\eta$ has compact support; (2) $\nabla u$ and $\nabla w$ are globally Lipschitz; (3) $V\in C^1$; (4) $-u+V\circ\nabla u$ is Lipschitz; and (5) almost everywhere,
--   $$\det\nabla^2u(x)=e^{-u(x)+V(\nabla u(x))}.$$
--   Then, with all integrals over Lebesgue volume on $\mathbb R^n$,
--
--   $$\int w(x)\left[\operatorname{tr}\!\left((\nabla^2u(x))^{-1}\nabla^2\eta(x)\right)-DV(\nabla u(x))[\nabla\eta(x)]\right]e^{-u(x)}\,dx$$
--   $$=-\int\sum_{i,j}(\nabla^2u(x))^{-1}_{ij}\,\partial_i\eta(x)\,\partial_jw(x)\,e^{-u(x)}\,dx.$$
--
--   This is a supporting weak integration-by-parts formula; it does not assert a KLS bound or additional regularity of $u$ or $w$.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integral_mul_generator_eq_neg_energy' {n : ℕ} {u V w η : EuclideanSpace ℝ (Fin n) → ℝ}
--       (hu : ContDiff ℝ 1 u) {G : NNReal} (hG : LipschitzWith G (gradient u)) (hV : ContDiff ℝ 1 V)
--       {LF : NNReal} (hF : LipschitzWith LF (fun x => -u x + V (gradient u x)))
--       (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
--         (hessianMatrix u x).det = Real.exp (-u x + V (gradient u x)))
--       (hw : ContDiff ℝ 1 w) {Gw : NNReal} (hGw : LipschitzWith Gw (gradient w))
--       (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η) :
--       ∫ x, w x * (((hessianMatrix u x)⁻¹ * hessianMatrix η x).trace -
--           fderiv ℝ V (gradient u x) (gradient η x)) * Real.exp (-u x)
--           ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) =
--         -∫ x, (∑ i, ∑ j, (hessianMatrix u x)⁻¹ i j *
--             fderiv ℝ η x (EuclideanSpace.basisFun (Fin n) ℝ i) *
--             fderiv ℝ w x (EuclideanSpace.basisFun (Fin n) ℝ j)) * Real.exp (-u x)
--           ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/IntegrationByParts/InverseHessian/Weak`](https://prove2.me/theorems/86db9ab2-0c2a-4dff-8904-eff1bba339a8).
--
--   Definition modules: [`Analysis/BakryEmery/HessianOperator`](https://prove2.me/theorems/0a60d77a-9d99-47ed-a649-6e1a28e13392), [`Analysis/Operator/Coordinates`](https://prove2.me/theorems/104936bd-b536-4e43-8bdb-e45d2e66c788).
--
--   Supporting theorems: [`integrable_inv_hessianMatrix_mul_of_bounded_compact`](https://prove2.me/theorems/a000c1ee-3b61-43e3-9151-d3b5dea77574), [`assemble_generator`](https://prove2.me/theorems/ecbe4dd5-bf64-4880-91be-e99fda5c9cf6), [`smooth_test_derivative`](https://prove2.me/theorems/a020d053-5b2e-45e7-bfaf-a25b6c53786c).
--
--   Previous: [`integral_mul_generator_eq_neg_energy`](https://prove2.me/theorems/eb1196e2-8044-4e2b-9000-8fcc401166ec) · Next: [`integrable_weak_generator_densities`](https://prove2.me/theorems/24449bc6-0de3-4efc-93a6-7a73a3bded73).
--
--   [Source excerpt, lines 798–811](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/InverseHessian/Weak.lean#L798-L811) · Frozen source `408915f`.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Theorem 2.5. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/InverseHessian/Weak.lean#L797-L847 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.InverseHessian.Weak`, declaration `FunctionalInequalities.Analysis.integral_mul_generator_eq_neg_energy'`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_InverseHessian_Weak

open MeasureTheory Set Filter
open FunctionalInequalities.Probability.Stein

theorem FunctionalInequalities.Analysis.integral_mul_generator_eq_neg_energy_prime_readable {n : ℕ} {u V w η : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u) {G : NNReal} (hG : LipschitzWith G (gradient u)) (hV : ContDiff ℝ 1 V)
    {LF : NNReal} (hF : LipschitzWith LF (fun x => -u x + V (gradient u x)))
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).det = Real.exp (-u x + V (gradient u x)))
    (hw : ContDiff ℝ 1 w) {Gw : NNReal} (hGw : LipschitzWith Gw (gradient w))
    (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η) :
    ∫ x, w x * (((hessianMatrix u x)⁻¹ * hessianMatrix η x).trace -
        fderiv ℝ V (gradient u x) (gradient η x)) * Real.exp (-u x)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) =
      -∫ x, (∑ i, ∑ j, (hessianMatrix u x)⁻¹ i j *
          fderiv ℝ η x (EuclideanSpace.basisFun (Fin n) ℝ i) *
          fderiv ℝ w x (EuclideanSpace.basisFun (Fin n) ℝ j)) * Real.exp (-u x)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by sorry
