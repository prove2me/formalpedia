-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_integral_mul_hessian_increment_le_readable
-- name    : FunctionalInequalities.Analysis.integral_mul_hessian_increment_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:50.28699+00:00
-- url     : https://prove2.me/theorems/ed5fdd74-9c13-4186-ad4f-40dd1e40ed9c
-- title:
--   Integrated Hessian Increment Energy Bound
-- statement:
--   This formalizes part of Theorem 2.5 of Letwin (arXiv:2607.24164v1), in the weak route.
--
--   Let $u,V,\eta:\mathbb R^n\to\mathbb R$. Assume: (1) $u,V\in C^1$ and are convex; (2) $\nabla u$ is Lipschitz; (3) $-u+V\circ\nabla u$ is Lipschitz; (4) for some $K>0$, almost everywhere $\nabla^2u(x)$ is positive definite, $\log\det\nabla^2u(x)=-u(x)+V(\nabla u(x))$, and $K I-\nabla^2u(x)$ is positive semidefinite; (5) $\eta\in C_c^2$ and $\eta\ge0$; and (6) for some $D\in\mathbb R$ and every $x,h$, $u(x+h)+u(x-h)-2u(x)\le D\|h\|^2$.
--
--   For every $h\in\mathbb R^n$,
--
--   $$\int \eta(x)\left(\|H(x+h)-H(x)\|_F^2+\|H(x-h)-H(x)\|_F^2\right)e^{-u(x)}\,dx$$
--   $$\le 2K^2D\|h\|^2\int\left|\eta(x)+L\eta(x)\right|e^{-u(x)}\,dx,$$
--
--   where $H=\operatorname{hessianMatrix}(u)$ and $L\eta=\operatorname{tr}(H^{-1}\operatorname{hessianMatrix}(\eta))-DV(\nabla u)[\nabla\eta]$.
--
--   The result is a weak integrated Hessian-increment estimate supporting, but not proving, the cited paper theorem.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integral_mul_hessian_increment_le {n : ℕ} {u V η : EuclideanSpace ℝ (Fin n) → ℝ}
--       (hu : ContDiff ℝ 1 u) (hconv : ConvexOn ℝ univ u) {G : NNReal}
--       (hG : LipschitzWith G (gradient u)) (hV : ContDiff ℝ 1 V) (hVc : ConvexOn ℝ univ V)
--       {LF : NNReal} (hF : LipschitzWith LF (fun x => -u x + V (gradient u x))) {K : ℝ} (hK : 0 < K)
--       (hdata : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
--         (hessianMatrix u x).PosDef ∧
--         Real.log (hessianMatrix u x).det = -u x + V (gradient u x) ∧
--         (K • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix u x).PosSemidef)
--       (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η) (hη0 : ∀ x, 0 ≤ η x) {D : ℝ}
--       (h : EuclideanSpace ℝ (Fin n)) (hw : ∀ x, u (x + h) + u (x - h) - 2 * u x ≤ D * ‖h‖ ^ 2) :
--       ∫ x, η x * ((∑ i, ∑ j, (hessianMatrix u (x + h) - hessianMatrix u x) i j ^ 2) +
--           ∑ i, ∑ j, (hessianMatrix u (x - h) - hessianMatrix u x) i j ^ 2) * Real.exp (-u x)
--           ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) ≤
--         2 * K ^ 2 * (D * ‖h‖ ^ 2) *
--           ∫ x, |η x + (((hessianMatrix u x)⁻¹ * hessianMatrix η x).trace -
--             fderiv ℝ V (gradient u x) (gradient η x))| * Real.exp (-u x)
--             ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/HessianIncrement`](https://prove2.me/theorems/ed30c0a7-e1f1-47c8-bf1b-4711117fdb53).
--
--   Definition modules: [`Analysis/BakryEmery/HessianOperator`](https://prove2.me/theorems/0a60d77a-9d99-47ed-a649-6e1a28e13392), [`Analysis/Operator/Coordinates`](https://prove2.me/theorems/104936bd-b536-4e43-8bdb-e45d2e66c788).
--
--   Selected supporting theorems: [`ae_hessian_increment_le_generator`](https://prove2.me/theorems/8a32f083-457a-427c-a413-4a9bda9a98fb), [`centeredDifference_contDiff_lipschitz_gradient`](https://prove2.me/theorems/4365f234-8db7-4310-8445-040bbe73e928), [`centeredDifference_nonneg_le`](https://prove2.me/theorems/9370319d-a121-4f26-8aa9-88be81cbf7e8), [`integrable_hessian_increment_energy`](https://prove2.me/theorems/629a963f-e2b8-40f9-bcc4-6dab330a953b), [`integrable_weak_generator_densities`](https://prove2.me/theorems/24449bc6-0de3-4efc-93a6-7a73a3bded73).
--
--   Previous: [`integrable_hessian_increment_energy`](https://prove2.me/theorems/629a963f-e2b8-40f9-bcc4-6dab330a953b) · Next: [`exists_hessian_cutoff_sq_difference_bound`](https://prove2.me/theorems/54515687-f5b2-40e0-b262-9c29f518ff9c).
--
--   [Source excerpt, lines 116–132](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/HessianIncrement.lean#L116-L132) · Frozen source `408915f`.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Theorem 2.5. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/HessianIncrement.lean#L111-L236 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.HessianIncrement`, declaration `FunctionalInequalities.Analysis.integral_mul_hessian_increment_le`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_HessianIncrement

open MeasureTheory Set Filter
open FunctionalInequalities.Probability.Stein

theorem FunctionalInequalities.Analysis.integral_mul_hessian_increment_le_readable {n : ℕ} {u V η : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u) (hconv : ConvexOn ℝ univ u) {G : NNReal}
    (hG : LipschitzWith G (gradient u)) (hV : ContDiff ℝ 1 V) (hVc : ConvexOn ℝ univ V)
    {LF : NNReal} (hF : LipschitzWith LF (fun x => -u x + V (gradient u x))) {K : ℝ} (hK : 0 < K)
    (hdata : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).PosDef ∧
      Real.log (hessianMatrix u x).det = -u x + V (gradient u x) ∧
      (K • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix u x).PosSemidef)
    (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η) (hη0 : ∀ x, 0 ≤ η x) {D : ℝ}
    (h : EuclideanSpace ℝ (Fin n)) (hw : ∀ x, u (x + h) + u (x - h) - 2 * u x ≤ D * ‖h‖ ^ 2) :
    ∫ x, η x * ((∑ i, ∑ j, (hessianMatrix u (x + h) - hessianMatrix u x) i j ^ 2) +
        ∑ i, ∑ j, (hessianMatrix u (x - h) - hessianMatrix u x) i j ^ 2) * Real.exp (-u x)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) ≤
      2 * K ^ 2 * (D * ‖h‖ ^ 2) *
        ∫ x, |η x + (((hessianMatrix u x)⁻¹ * hessianMatrix η x).trace -
          fderiv ℝ V (gradient u x) (gradient η x))| * Real.exp (-u x)
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by sorry
