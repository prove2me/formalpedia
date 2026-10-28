-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_integral_exp_neg_hessian_flux_eq_curvature_gram_readable
-- name    : FunctionalInequalities.Analysis.integral_exp_neg_hessian_flux_eq_curvature_gram_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:06:01.410273+00:00
-- url     : https://prove2.me/theorems/6d3ddc0c-45c1-4c79-b3d0-33799314293f
-- title:
--   Weighted Weak Hessian Evolution with Curvature and Gram Forcing
-- statement:
--   This formalizes part of Lemma 2.4 of Letwin (arXiv:2607.24164v1).
--
--   Let $u,W:\mathbb R^n\to\mathbb R$ satisfy: $u$ is $C^1$ and Lipschitz; $\nabla u$ is Lipschitz; $W$ is $C^2$; and $-u+W\circ\nabla u$ is Lipschitz. Assume
--   $$
--   \det\nabla^2u=\exp(-u+W(\nabla u))
--   $$
--   a.e. Let $T_{kij}$ be a weak Hessian tensor, with the stated weak derivatives, compact-local $L^2$ bounds, and compact-local `ENNReal` $L^\infty$ bounds for the inverse Hessian. Assume also that the trace of $(\nabla^2u)^{-1}T_i$ has the prescribed a.e. first Monge–Ampère derivative.
--
--   Set
--   $$
--   R=(\nabla^2u)^{-1},\qquad J_{ija}=\sum_bR_{ba}T_{bij},
--   $$
--   and
--   $$
--   E_{ij}=-(\nabla^2u)_{ij}
--   +(\nabla^2u\,\nabla^2W(\nabla u)\,\nabla^2u)_{ij}
--   +\operatorname{tr}(RT_iRT_j).
--   $$
--   Then for every $i,j$, $J_{ija}$ is compact-locally in $L^2$, both $E_{ij}$ and $e^{-u}E_{ij}$ are locally integrable, and every compactly supported $C^1$ function $\psi$ satisfies
--
--   $$
--   \int e^{-u(x)}\sum_aJ_{ija}(x)\,\partial_a\psi(x)\,dx
--   =-\int e^{-u(x)}E_{ij}(x)\psi(x)\,dx.
--   $$
--
--   This is the principal weighted weak Hessian-evolution identity and is reusable for subsequent testing arguments.
--
--   **Original Lean conclusion excerpt**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Earlier hypotheses and the proof are omitted from this excerpt; the complete verified statement remains below.
--
--   ```lean
--             ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
--         LocallyIntegrable (fun x => E x i j)
--           (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
--         LocallyIntegrable (fun x => Real.exp (-u x) * E x i j)
--           (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
--         ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
--           ContDiff ℝ 1 ψ → HasCompactSupport ψ →
--           (∫ x, Real.exp (-u x) * (∑ a : Fin n, J x i j a *
--             fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ a))
--             ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
--           -(∫ x, Real.exp (-u x) * E x i j * ψ x
--             ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/IntegrationByParts/WeakHessianEvolution`](https://prove2.me/theorems/d20d941d-a690-4ebe-9a63-a346adf8dd16).
--
--   Definition modules: [`Analysis/BakryEmery/HessianOperator`](https://prove2.me/theorems/0a60d77a-9d99-47ed-a649-6e1a28e13392), [`Analysis/Operator/Coordinates`](https://prove2.me/theorems/104936bd-b536-4e43-8bdb-e45d2e66c788), [`Analysis/WeakDerivative/Basic`](https://prove2.me/theorems/5af72772-2fc4-48c4-926f-dd1d449f0f11).
--
--   Supporting theorems: [`HasWeakDerivAlong.congr_ae`](https://prove2.me/theorems/feacd1e3-2d93-4444-8c84-fe52a0849220), [`hasWeakDerivAlong_mongeAmpere_first_rhs`](https://prove2.me/theorems/55f12f10-6c36-4776-96b3-387313b3b590), [`integral_weak_hessian_flux_eq_trace_derivative`](https://prove2.me/theorems/6d0b46f6-29ee-4cf1-8e3f-098cb8c41989), [`ae_hessian_flux_forcing_minus_drift`](https://prove2.me/theorems/838d3785-b396-43ff-b452-a1eb6e64d796), [`integral_exp_neg_flux_of_unweighted`](https://prove2.me/theorems/ede33e09-7e75-4497-9ed6-66486b1825c1).
--
--   Previous: [`integral_exp_neg_flux_of_unweighted`](https://prove2.me/theorems/ede33e09-7e75-4497-9ed6-66486b1825c1) · Next: [`integral_exp_neg_hessian_flux_eq_curvature_gram_of_bounded_weak_test`](https://prove2.me/theorems/6c225a3e-8283-4741-ad77-ae9ad7405baf).
--
--   [Source excerpt, lines 1441–1452](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/WeakHessianEvolution.lean#L1441-L1452) · Frozen source `408915f`.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Lemma 2.4. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/WeakHessianEvolution.lean#L1396-L1585 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.WeakHessianEvolution`, declaration `FunctionalInequalities.Analysis.integral_exp_neg_hessian_flux_eq_curvature_gram`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_WeakHessianEvolution

open Matrix MeasureTheory Set Filter
open FunctionalInequalities.Probability.Stein
set_option maxHeartbeats 1200000

theorem FunctionalInequalities.Analysis.integral_exp_neg_hessian_flux_eq_curvature_gram_readable {n : ℕ}
    {u W : EuclideanSpace ℝ (Fin n) → ℝ} {L G LF : NNReal}
    (hu : ContDiff ℝ 1 u) (hL : LipschitzWith L u)
    (hG : LipschitzWith G (gradient u)) (hW : ContDiff ℝ 2 W)
    (hF : LipschitzWith LF (fun x => -u x + W (gradient u x)))
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).det = Real.exp (-u x + W (gradient u x)))
    (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ)
    (hT : ∀ k i j : Fin n,
      HasWeakDerivAlong (fun x => hessianMatrix u x i j) (fun x => T x k i j)
        (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => T x k i j) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hInv : ∀ k i j : Fin n,
        HasWeakDerivAlong (fun x => (hessianMatrix u x)⁻¹ i j)
          (fun x => -(((hessianMatrix u x)⁻¹ *
            (Matrix.of fun a b => T x k a b) * (hessianMatrix u x)⁻¹) i j))
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        (∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => -(((hessianMatrix u x)⁻¹ *
            (Matrix.of fun a b => T x k a b) * (hessianMatrix u x)⁻¹) i j))
            2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
        ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => (hessianMatrix u x)⁻¹ i j) (⊤ : ENNReal)
            ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hFirst : ∀ i : Fin n,
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        ((hessianMatrix u x)⁻¹ * (Matrix.of fun a b => T x i a b)).trace =
          -fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ i) +
          ∑ a : Fin n, hessianMatrix u x i a *
            fderiv ℝ W (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ a)) :
    let R := fun x => (hessianMatrix u x)⁻¹
    let J := fun x i j a => ∑ b : Fin n, R x b a * T x b i j
    let E := fun x i j => -hessianMatrix u x i j +
      (hessianMatrix u x * hessianMatrix W (gradient u x) * hessianMatrix u x) i j +
      (R x * (Matrix.of fun a b => T x i a b) * R x *
        (Matrix.of fun a b => T x j a b)).trace
    ∀ i j : Fin n,
      (∀ a : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => J x i j a) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      LocallyIntegrable (fun x => E x i j)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      LocallyIntegrable (fun x => Real.exp (-u x) * E x i j)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
        ContDiff ℝ 1 ψ → HasCompactSupport ψ →
        (∫ x, Real.exp (-u x) * (∑ a : Fin n, J x i j a *
          fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ a))
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        -(∫ x, Real.exp (-u x) * E x i j * ψ x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by sorry
