-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_assemble_generator_readable
-- name    : FunctionalInequalities.Analysis.assemble_generator_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:37.208958+00:00
-- url     : https://prove2.me/theorems/ecbe4dd5-bf64-4880-91be-e99fda5c9cf6
-- title:
--   Assembly of the Weak Generator Identity
-- statement:
--   This is an assembly lemma for a weak inverse-Hessian generator identity.
--
--   Let $u,V,a,f$ be functions on $\operatorname{EuclideanSpace}\,\mathbb R\,(\operatorname{Fin}(n))$. Assume $u,V$ are $C^1$, $\nabla u$ is Lipschitz, the exponent $-u+V\circ\nabla u$ is Lipschitz, and almost everywhere
--   $$\det(\operatorname{hessianMatrix}(u,x))=e^{-u(x)+V(\nabla u(x))}.$$
--   Assume also that each weighted coordinate test has a Lipschitz compactly supported representative, that its coordinate derivative satisfies the specified a.e. formula, and that the associated `energyDensity u a f` is integrable.
--
--   Then
--   $$\int \operatorname{generatorDensity}(u,V,a,f)\,d\operatorname{vol}
--   =-\int \operatorname{energyDensity}(u,a,f)\,d\operatorname{vol}.$$
--
--   The statement is an internal analytic assembly interface: its hypotheses include the derivative and integrability inputs explicitly, and it does not itself assert the broader Monge–Ampère theorem.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   private lemma assemble_generator {n : ℕ}
--       {u V a f : EuclideanSpace ℝ (Fin n) → ℝ}
--       (hu : ContDiff ℝ 1 u) {G : NNReal}
--       (hG : LipschitzWith G (gradient u)) (hV : ContDiff ℝ 1 V)
--       {LF : NNReal} (hF : LipschitzWith LF (fun x => -u x + V (gradient u x)))
--       (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
--         (hessianMatrix u x).det = Real.exp (-u x + V (gradient u x)))
--       (ht : ∀ i, ∃ L : NNReal,
--         LipschitzWith L (weightedTest u a f i) ∧
--           HasCompactSupport (weightedTest u a f i))
--       (hd : ∀ i, ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), ∀ j,
--         coord (weightedTest u a f i) j x =
--           Real.exp (-u x) *
--             (coord a j x * coord f i x -
--               a x * coord u j x * coord f i x +
--               a x * hessianMatrix f x j i))
--       (hE : Integrable (energyDensity u a f)
--         (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
--       (∫ x, generatorDensity u V a f x
--         ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
--           -∫ x, energyDensity u a f x
--             ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/IntegrationByParts/InverseHessian/Weak`](https://prove2.me/theorems/86db9ab2-0c2a-4dff-8904-eff1bba339a8).
--
--   Definition modules: [`Analysis/BakryEmery/HessianOperator`](https://prove2.me/theorems/0a60d77a-9d99-47ed-a649-6e1a28e13392).
--
--   Supporting theorems: [`ae_fderiv_mongeAmpere_exponent`](https://prove2.me/theorems/71049741-6710-4957-9e2a-2a505bfab529), [`integrable_inv_hessianMatrix_mul_of_bounded_compact`](https://prove2.me/theorems/a000c1ee-3b61-43e3-9151-d3b5dea77574), [`sum_integral_inv_hessianMatrix_mul_fderiv_eq`](https://prove2.me/theorems/6b9e4f58-2fc3-4a95-b0cc-1514a275dd70), [`sum_inv_gradient_test_sub_chain_eq`](https://prove2.me/theorems/7266b246-03c7-419d-a30f-6d99183cc1fc).
--
--   Previous: [`smooth_test_derivative`](https://prove2.me/theorems/a020d053-5b2e-45e7-bfaf-a25b6c53786c) · Next: [`integral_mul_generator_eq_neg_energy`](https://prove2.me/theorems/eb1196e2-8044-4e2b-9000-8fcc401166ec).
--
--   [Source excerpt, lines 602–623](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/InverseHessian/Weak.lean#L602-L623) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/InverseHessian/Weak.lean#L602-L742 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.InverseHessian.Weak`, declaration `_private.FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.InverseHessian.Weak.0.FunctionalInequalities.Analysis.assemble_generator`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_InverseHessian_Weak

open MeasureTheory Set Filter
open FunctionalInequalities.Probability.Stein

lemma FunctionalInequalities.Analysis.assemble_generator_readable {n : ℕ}
    {u V a f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u) {G : NNReal}
    (hG : LipschitzWith G (gradient u)) (hV : ContDiff ℝ 1 V)
    {LF : NNReal} (hF : LipschitzWith LF (fun x => -u x + V (gradient u x)))
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).det = Real.exp (-u x + V (gradient u x)))
    (ht : ∀ i, ∃ L : NNReal,
      LipschitzWith L (FunctionalInequalities.Analysis.weightedTest u a f i) ∧
        HasCompactSupport (FunctionalInequalities.Analysis.weightedTest u a f i))
    (hd : ∀ i, ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), ∀ j,
      FunctionalInequalities.Analysis.coord (FunctionalInequalities.Analysis.weightedTest u a f i) j x =
        Real.exp (-u x) *
          (FunctionalInequalities.Analysis.coord a j x * FunctionalInequalities.Analysis.coord f i x -
            a x * FunctionalInequalities.Analysis.coord u j x * FunctionalInequalities.Analysis.coord f i x +
            a x * hessianMatrix f x j i))
    (hE : Integrable (FunctionalInequalities.Analysis.energyDensity u a f)
      (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    (∫ x, FunctionalInequalities.Analysis.generatorDensity u V a f x
      ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        -∫ x, FunctionalInequalities.Analysis.energyDensity u a f x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by sorry
