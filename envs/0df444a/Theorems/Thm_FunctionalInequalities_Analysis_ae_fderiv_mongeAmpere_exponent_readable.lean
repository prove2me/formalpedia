-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_ae_fderiv_mongeAmpere_exponent_readable
-- name    : FunctionalInequalities.Analysis.ae_fderiv_mongeAmpere_exponent_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:03:33.607636+00:00
-- url     : https://prove2.me/theorems/71049741-6710-4957-9e2a-2a505bfab529
-- title:
--   Almost-Everywhere Derivative of the Monge–Ampère Exponent
-- statement:
--   This formalizes the coordinate chain-rule identity associated with the Monge–Ampère exponent, cited as a partial formalization of Lemma 2.4 of Letwin (arXiv:2607.24164v1).
--
--   Let $n\in\mathbb N$ and let $u,V:\operatorname{EuclideanSpace}(\mathbb R,\operatorname{Fin}(n))\to\mathbb R$. Assume:
--
--   1. $u$ is $C^1$.
--   2. Its gradient is Lipschitz with some constant $G\in[0,\infty)$.
--   3. $V$ is $C^1$.
--
--   Then, for almost every $x$ and every coordinate index $j<n$,
--
--   $$D\bigl[-u+V\circ\nabla u\bigr](x)e_j
--   =-Du(x)e_j+\sum_{k<n}H_u(x)_{jk}\,DV(\nabla u(x))e_k,$$
--
--   where $H_u$ is the coordinate matrix `hessianMatrix`, and $e_j$ is `EuclideanSpace.basisFun (Fin n) ℝ j`. The declaration is a coordinate identity only; it does not assert a Monge–Ampère equation.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem ae_fderiv_mongeAmpere_exponent {n : ℕ}
--       {u V : EuclideanSpace ℝ (Fin n) → ℝ}
--       (hu : ContDiff ℝ 1 u) {G : NNReal} (hG : LipschitzWith G (gradient u))
--       (hV : ContDiff ℝ 1 V) :
--       ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), ∀ j : Fin n,
--         fderiv ℝ (fun y => -u y + V (gradient u y)) x
--             (EuclideanSpace.basisFun (Fin n) ℝ j) =
--           -fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ j) +
--             ∑ k, hessianMatrix u x j k *
--               fderiv ℝ V (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ k)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/IntegrationByParts/InverseHessian/Weak`](https://prove2.me/theorems/86db9ab2-0c2a-4dff-8904-eff1bba339a8).
--
--   Definition modules: [`Analysis/BakryEmery/HessianOperator`](https://prove2.me/theorems/0a60d77a-9d99-47ed-a649-6e1a28e13392).
--
--   Next: [`sum_inv_gradient_test_sub_chain_eq`](https://prove2.me/theorems/7266b246-03c7-419d-a30f-6d99183cc1fc).
--
--   [Source excerpt, lines 220–229](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/InverseHessian/Weak.lean#L220-L229) · Frozen source `408915f`.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Lemma 2.4. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/InverseHessian/Weak.lean#L218-L296 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.InverseHessian.Weak`, declaration `FunctionalInequalities.Analysis.ae_fderiv_mongeAmpere_exponent`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_InverseHessian_Weak

open MeasureTheory
open FunctionalInequalities.Probability.Stein

theorem FunctionalInequalities.Analysis.ae_fderiv_mongeAmpere_exponent_readable {n : ℕ}
    {u V : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u) {G : NNReal} (hG : LipschitzWith G (gradient u))
    (hV : ContDiff ℝ 1 V) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), ∀ j : Fin n,
      fderiv ℝ (fun y => -u y + V (gradient u y)) x
          (EuclideanSpace.basisFun (Fin n) ℝ j) =
        -fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ j) +
          ∑ k, hessianMatrix u x j k *
            fderiv ℝ V (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ k) := by sorry
