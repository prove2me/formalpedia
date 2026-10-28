-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_ae_hessian_increment_le_generator_readable
-- name    : FunctionalInequalities.Analysis.ae_hessian_increment_le_generator_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:03:40.171622+00:00
-- url     : https://prove2.me/theorems/8a32f083-457a-427c-a413-4a9bda9a98fb
-- title:
--   Almost-Everywhere Hessian Increment Coercivity
-- statement:
--   This is a partial formalization of the Hessian coercivity statement associated with Lemma 2.4 of Letwin (arXiv:2607.24164v1).
--
--   Let $n\in\mathbb N$ and let $u,V:\operatorname{EuclideanSpace}(\mathbb R,\operatorname{Fin}(n))\to\mathbb R$. Assume:
--
--   1. $u$ is $C^1$ and $\nabla u$ is Lipschitz.
--   2. $V$ is differentiable and convex on the whole space.
--   3. For almost every $x$, with $H(x)=\operatorname{hessianMatrix}(u,x)$, $H(x)$ is positive definite,
--      $$\log\det H(x)=-u(x)+V(\nabla u(x)),$$
--      and $K I-H(x)$ is positive semidefinite.
--
--   For every increment $h$, for almost every $x$,
--
--   $$\frac{\|H(x+h)-H(x)\|_F^2+\|H(x-h)-H(x)\|_F^2}{2K^2}
--   \le \operatorname{tr}\!\left(H(x)^{-1}H_w(x)\right)
--   -DV(\nabla u(x))(\nabla w(x))+w(x),$$
--
--   where $w(y)=u(y+h)+u(y-h)-2u(y)$ and $H_w=\operatorname{hessianMatrix}(w,\cdot)$. The almost-everywhere qualifier is with respect to Lebesgue measure, and no positivity of $K$ is separately assumed.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem ae_hessian_increment_le_generator {n : ℕ} {u V : EuclideanSpace ℝ (Fin n) → ℝ}
--       (hu : ContDiff ℝ 1 u) {G : NNReal} (hG : LipschitzWith G (gradient u))
--       (hV : Differentiable ℝ V) (hVc : ConvexOn ℝ univ V) {K : ℝ}
--       (hdata : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
--         (hessianMatrix u x).PosDef ∧
--         Real.log (hessianMatrix u x).det = -u x + V (gradient u x) ∧
--         (K • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix u x).PosSemidef)
--       (h : EuclideanSpace ℝ (Fin n)) :
--       ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
--         ((∑ i, ∑ j, (hessianMatrix u (x + h) - hessianMatrix u x) i j ^ 2) +
--             ∑ i, ∑ j, (hessianMatrix u (x - h) - hessianMatrix u x) i j ^ 2) / (2 * K ^ 2) ≤
--           ((hessianMatrix u x)⁻¹ *
--               hessianMatrix (fun y => u (y + h) + u (y - h) - 2 * u y) x).trace -
--             fderiv ℝ V (gradient u x) (gradient (fun y => u (y + h) + u (y - h) - 2 * u y) x) +
--             (u (x + h) + u (x - h) - 2 * u x)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/Viscosity`](https://prove2.me/theorems/a4ce95cb-0230-40ed-bbee-de7462504a4b).
--
--   Definition modules: [`Analysis/BakryEmery/HessianOperator`](https://prove2.me/theorems/0a60d77a-9d99-47ed-a649-6e1a28e13392), [`Analysis/Operator/Coordinates`](https://prove2.me/theorems/104936bd-b536-4e43-8bdb-e45d2e66c788).
--
--   Supporting theorems: [`log_det_add_frobenius_sq_le`](https://prove2.me/theorems/42e7e2e1-c8f2-4cb8-b154-81b11d6da306).
--
--   Previous: [`exists_penalized_maximum_with_comparison`](https://prove2.me/theorems/511a8bb6-640f-477b-98fa-7c8e07f3450e).
--
--   [Source excerpt, lines 1920–1934](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/Viscosity.lean#L1920-L1934) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Viscosity.lean#L1916-L1970 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Viscosity`, declaration `FunctionalInequalities.Analysis.ae_hessian_increment_le_generator`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Viscosity

open FunctionalInequalities.Probability.Stein
open MeasureTheory Set Filter

theorem FunctionalInequalities.Analysis.ae_hessian_increment_le_generator_readable {n : ℕ} {u V : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u) {G : NNReal} (hG : LipschitzWith G (gradient u))
    (hV : Differentiable ℝ V) (hVc : ConvexOn ℝ univ V) {K : ℝ}
    (hdata : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).PosDef ∧
      Real.log (hessianMatrix u x).det = -u x + V (gradient u x) ∧
      (K • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix u x).PosSemidef)
    (h : EuclideanSpace ℝ (Fin n)) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      ((∑ i, ∑ j, (hessianMatrix u (x + h) - hessianMatrix u x) i j ^ 2) +
          ∑ i, ∑ j, (hessianMatrix u (x - h) - hessianMatrix u x) i j ^ 2) / (2 * K ^ 2) ≤
        ((hessianMatrix u x)⁻¹ *
            hessianMatrix (fun y => u (y + h) + u (y - h) - 2 * u y) x).trace -
          fderiv ℝ V (gradient u x) (gradient (fun y => u (y + h) + u (y - h) - 2 * u y) x) +
          (u (x + h) + u (x - h) - 2 * u x) := by sorry
