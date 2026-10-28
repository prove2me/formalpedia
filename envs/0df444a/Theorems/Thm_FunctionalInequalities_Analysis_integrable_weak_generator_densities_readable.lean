-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_integrable_weak_generator_densities_readable
-- name    : FunctionalInequalities.Analysis.integrable_weak_generator_densities_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:46.894698+00:00
-- url     : https://prove2.me/theorems/24449bc6-0de3-4efc-93a6-7a73a3bded73
-- title:
--   Integrability of Weak Inverse-Hessian Generator Densities
-- statement:
--   This is an integrability component related to Theorem 2.5 of Letwin (arXiv:2607.24164v1).
--
--   Let $u,V,w,\eta$ be functions on $\operatorname{EuclideanSpace}\,\mathbb R\,(\operatorname{Fin}(n))$. Assume:
--
--   1. $u$ is continuous and has Lipschitz gradient;
--   2. $V$ is $C^1$;
--   3. $x\mapsto-u(x)+V(\nabla u(x))$ is continuous and, almost everywhere, $\det H_u(x)=e^{-u(x)+V(\nabla u(x))}$;
--   4. $w$ is continuous with Lipschitz gradient;
--   5. $\eta$ is $C^2$ and compactly supported.
--
--   Then each of the following is integrable with respect to volume:
--
--   $$\eta\left(\operatorname{tr}(H_u^{-1}H_w)-DV(\nabla u)(\nabla w)\right)e^{-u},$$
--   $$w\left(\operatorname{tr}(H_u^{-1}H_\eta)-DV(\nabla u)(\nabla\eta)\right)e^{-u},$$
--   and
--   $$\left|\eta+\operatorname{tr}(H_u^{-1}H_\eta)-DV(\nabla u)(\nabla\eta)\right|e^{-u}.$$
--
--   Here $H_u$ denotes `hessianMatrix u`; all determinant hypotheses are a.e. statements. The result establishes integrability needed for weak generator identities, not those identities themselves.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integrable_weak_generator_densities {n : ℕ}
--       {u V w η : EuclideanSpace ℝ (Fin n) → ℝ}
--       (hu : Continuous u) {G : NNReal} (hG : LipschitzWith G (gradient u))
--       (hV : ContDiff ℝ 1 V)
--       (hF : Continuous (fun x => -u x + V (gradient u x)))
--       (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
--         (hessianMatrix u x).det = Real.exp (-u x + V (gradient u x)))
--       (hw : Continuous w) {Gw : NNReal} (hGw : LipschitzWith Gw (gradient w))
--       (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η) :
--       Integrable (fun x => η x *
--         (((hessianMatrix u x)⁻¹ * hessianMatrix w x).trace -
--           fderiv ℝ V (gradient u x) (gradient w x)) * Real.exp (-u x))
--         (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
--       Integrable (fun x => w x *
--         (((hessianMatrix u x)⁻¹ * hessianMatrix η x).trace -
--           fderiv ℝ V (gradient u x) (gradient η x)) * Real.exp (-u x))
--         (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
--       Integrable (fun x =>
--         |η x + (((hessianMatrix u x)⁻¹ * hessianMatrix η x).trace -
--           fderiv ℝ V (gradient u x) (gradient η x))| * Real.exp (-u x))
--         (volume : Measure (EuclideanSpace ℝ (Fin n)))
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/IntegrationByParts/InverseHessian/Weak`](https://prove2.me/theorems/86db9ab2-0c2a-4dff-8904-eff1bba339a8).
--
--   Definition modules: [`Analysis/BakryEmery/HessianOperator`](https://prove2.me/theorems/0a60d77a-9d99-47ed-a649-6e1a28e13392), [`Analysis/Operator/Coordinates`](https://prove2.me/theorems/104936bd-b536-4e43-8bdb-e45d2e66c788).
--
--   Supporting theorems: [`integrable_inv_hessianMatrix_mul_of_bounded_compact`](https://prove2.me/theorems/a000c1ee-3b61-43e3-9151-d3b5dea77574), [`norm_hessianMatrix_entry_le_of_lipschitz_gradient`](https://prove2.me/theorems/c390fe75-eaf1-41ee-934b-fddb8427fab6).
--
--   Previous: [`integral_mul_generator_eq_neg_energy'`](https://prove2.me/theorems/12ffe5ab-1e01-479f-819d-012727f89a87) · Next: [`hasWeakDerivAlong_inverse_hessian_of_logdet`](https://prove2.me/theorems/6e913d0c-8e93-456f-8534-533355d49266).
--
--   [Source excerpt, lines 889–909](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/InverseHessian/Weak.lean#L889-L909) · Frozen source `408915f`.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Theorem 2.5. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/InverseHessian/Weak.lean#L887-L1038 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.InverseHessian.Weak`, declaration `FunctionalInequalities.Analysis.integrable_weak_generator_densities`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_InverseHessian_Weak

open MeasureTheory Set Filter
open FunctionalInequalities.Probability.Stein

theorem FunctionalInequalities.Analysis.integrable_weak_generator_densities_readable {n : ℕ}
    {u V w η : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : Continuous u) {G : NNReal} (hG : LipschitzWith G (gradient u))
    (hV : ContDiff ℝ 1 V)
    (hF : Continuous (fun x => -u x + V (gradient u x)))
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).det = Real.exp (-u x + V (gradient u x)))
    (hw : Continuous w) {Gw : NNReal} (hGw : LipschitzWith Gw (gradient w))
    (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η) :
    Integrable (fun x => η x *
      (((hessianMatrix u x)⁻¹ * hessianMatrix w x).trace -
        fderiv ℝ V (gradient u x) (gradient w x)) * Real.exp (-u x))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    Integrable (fun x => w x *
      (((hessianMatrix u x)⁻¹ * hessianMatrix η x).trace -
        fderiv ℝ V (gradient u x) (gradient η x)) * Real.exp (-u x))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    Integrable (fun x =>
      |η x + (((hessianMatrix u x)⁻¹ * hessianMatrix η x).trace -
        fderiv ℝ V (gradient u x) (gradient η x))| * Real.exp (-u x))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by sorry
