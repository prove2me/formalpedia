-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_integral_exp_neg_hessian_flux_eq_curvature_gram_of_bounded_weak_test_readable
-- name    : FunctionalInequalities.Analysis.integral_exp_neg_hessian_flux_eq_curvature_gram_of_bounded_weak_test_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:06:12.576339+00:00
-- url     : https://prove2.me/theorems/6c225a3e-8283-4741-ad77-ae9ad7405baf
-- title:
--   Weighted Hessian Evolution for Bounded Weak Tests
-- statement:
--   This formalizes the bounded-test extension of part of Lemma 2.4 of Letwin (arXiv:2607.24164v1).
--
--   Under the hypotheses of the weighted weak Hessian evolution, let $u,W,T$ and the weak derivative data satisfy the same regularity, Monge–Ampère, compact-local $L^2$, inverse-Hessian `ENNReal` local $L^\infty$, and a.e. trace assumptions as in `integral_exp_neg_hessian_flux_eq_curvature_gram_readable`. Let $\eta$ be locally integrable and bounded by $C$, with compact support. For each coordinate $b$, assume $a_b$ is a weak derivative of $\eta$ in the $b$-th direction, is compactly supported, and belongs globally to $L^2$.
--
--   With
--   $$
--   R=(\nabla^2u)^{-1},\quad J_{ijb}=\sum_cR_{cb}T_{cij},
--   $$
--   and
--   $$
--   E_{ij}=-(\nabla^2u)_{ij}
--   +(\nabla^2u\,\nabla^2W(\nabla u)\,\nabla^2u)_{ij}
--   +\operatorname{tr}(RT_iRT_j),
--   $$
--   then, for every $i,j$, the products $e^{-u}J_{ijb}a_b$ and $e^{-u}E_{ij}\eta$ are integrable and
--
--   $$
--   \int e^{-u(x)}\sum_bJ_{ijb}(x)a_b(x)\,dx
--   =-\int e^{-u(x)}E_{ij}(x)\eta(x)\,dx.
--   $$
--
--   This provides the rough-test form of the weighted evolution identity for later weak and cutoff arguments.
--
--   **Original Lean conclusion excerpt**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Earlier hypotheses and the proof are omitted from this excerpt; the complete verified statement remains below.
--
--   ```lean
--         (R x * (Matrix.of fun a b => T x i a b) * R x *
--           (Matrix.of fun a b => T x j a b)).trace
--       ∀ i j : Fin n,
--         (∀ b : Fin n, Integrable
--           (fun x => Real.exp (-u x) * J x i j b * a b x)
--           (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
--         Integrable (fun x => Real.exp (-u x) * E x i j * η x)
--           (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
--         (∫ x, Real.exp (-u x) * (∑ b : Fin n, J x i j b * a b x)
--           ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
--         -(∫ x, Real.exp (-u x) * E x i j * η x
--           ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/IntegrationByParts/WeakHessianEvolution`](https://prove2.me/theorems/d20d941d-a690-4ebe-9a63-a346adf8dd16).
--
--   Definition modules: [`Analysis/BakryEmery/HessianOperator`](https://prove2.me/theorems/0a60d77a-9d99-47ed-a649-6e1a28e13392), [`Analysis/Operator/Coordinates`](https://prove2.me/theorems/104936bd-b536-4e43-8bdb-e45d2e66c788), [`Analysis/WeakDerivative/Basic`](https://prove2.me/theorems/5af72772-2fc4-48c4-926f-dd1d449f0f11).
--
--   Supporting theorems: [`integral_exp_neg_hessian_flux_eq_curvature_gram`](https://prove2.me/theorems/6d3ddc0c-45c1-4c79-b3d0-33799314293f), [`integral_flux_eq_neg_forcing_of_bounded_weak_test`](https://prove2.me/theorems/a62894bf-0470-4e04-8a24-6f8073da24d8).
--
--   Previous: [`integral_exp_neg_hessian_flux_eq_curvature_gram`](https://prove2.me/theorems/6d3ddc0c-45c1-4c79-b3d0-33799314293f).
--
--   [Source excerpt, lines 1658–1669](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/WeakHessianEvolution.lean#L1658-L1669) · Frozen source `408915f`.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Theorem 2.5. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/WeakHessianEvolution.lean#L1613-L1711 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.WeakHessianEvolution`, declaration `FunctionalInequalities.Analysis.integral_exp_neg_hessian_flux_eq_curvature_gram_of_bounded_weak_test`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_WeakHessianEvolution

open MeasureTheory Set Filter
open FunctionalInequalities.Probability.Stein

theorem FunctionalInequalities.Analysis.integral_exp_neg_hessian_flux_eq_curvature_gram_of_bounded_weak_test_readable {n : ℕ}
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
            (Matrix.of fun a b => T x k a b) * (hessianMatrix u x)⁻¹) i j)) 2
            ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
        ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => (hessianMatrix u x)⁻¹ i j) (⊤ : ENNReal)
            ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hFirst : ∀ i : Fin n,
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        ((hessianMatrix u x)⁻¹ * (Matrix.of fun a b => T x i a b)).trace =
          -fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ i) +
          ∑ a : Fin n, hessianMatrix u x i a *
            fderiv ℝ W (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ a))
    {η : EuclideanSpace ℝ (Fin n) → ℝ}
    {a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ} {C : ℝ}
    (hη : LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hbound : ∀ x, ‖η x‖ ≤ C) (hηc : HasCompactSupport η)
    (hweak : ∀ b : Fin n, HasWeakDerivAlong η (a b) (EuclideanSpace.basisFun (Fin n) ℝ b))
    (hac : ∀ b : Fin n, HasCompactSupport (a b))
    (ha2 : ∀ b : Fin n, MemLp (a b) 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    let R := fun x => (hessianMatrix u x)⁻¹
    let J := fun x i j a => ∑ b : Fin n, R x b a * T x b i j
    let E := fun x i j => -hessianMatrix u x i j +
      (hessianMatrix u x * hessianMatrix W (gradient u x) * hessianMatrix u x) i j +
      (R x * (Matrix.of fun a b => T x i a b) * R x *
        (Matrix.of fun a b => T x j a b)).trace
    ∀ i j : Fin n,
      (∀ b : Fin n, Integrable
        (fun x => Real.exp (-u x) * J x i j b * a b x)
        (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
      Integrable (fun x => Real.exp (-u x) * E x i j * η x)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      (∫ x, Real.exp (-u x) * (∑ b : Fin n, J x i j b * a b x)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      -(∫ x, Real.exp (-u x) * E x i j * η x
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by sorry
