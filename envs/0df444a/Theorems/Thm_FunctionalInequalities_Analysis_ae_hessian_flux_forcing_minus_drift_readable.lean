-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_ae_hessian_flux_forcing_minus_drift_readable
-- name    : FunctionalInequalities.Analysis.ae_hessian_flux_forcing_minus_drift_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:06:11.724746+00:00
-- url     : https://prove2.me/theorems/838d3785-b396-43ff-b452-a1eb6e64d796
-- title:
--   Almost-Everywhere Hessian Flux Forcing Decomposition
-- statement:
--   This is an almost-everywhere algebraic identity associated with the weak second Hessian evolution.
--
--   Let $u,W:\mathbb R^n\to\mathbb R$ be such that $u$ is $C^1$ with Lipschitz gradient, $W$ is $C^2$, and $-u+W\circ\nabla u$ is Lipschitz. Assume
--   $$
--   \det\nabla^2u(x)=\exp\bigl(-u(x)+W(\nabla u(x))\bigr)
--   $$
--   a.e. Assume a weak Hessian tensor $T$ and weak inverse-Hessian derivatives with the compact-local $L^2$ and `ENNReal`-valued local $L^\infty$ hypotheses stated in the declaration.
--
--   With
--   $$
--   R=(\nabla^2u)^{-1},\quad D_{kba}=-(RT_kR)_{ba},\quad
--   J_{ija}=\sum_bR_{ba}T_{bij},
--   $$
--   and
--   $$
--   Q_{ij}=-(\nabla^2u)_{ji}+\sum_a\left(T_{jia}\,\partial_aW(\nabla u)
--   +(\nabla^2u)_{ia}\sum_b(\nabla^2u)_{jb}(\nabla^2W)_{ba}(\nabla u)\right),
--   $$
--   the following equality holds for almost every $x$, simultaneously for all $i,j$:
--
--   $$
--   Q_{ij}-\sum_{a,b}T_{iab}D_{jba}
--   +\sum_bT_{bij}\sum_aD_{aba}
--   -\sum_aJ_{ija}\,\partial_a u
--   =
--   -(\nabla^2u)_{ij}
--   +(\nabla^2u\,\nabla^2W(\nabla u)\,\nabla^2u)_{ij}
--   +\operatorname{tr}(RT_iRT_j).
--   $$
--
--   This lemma identifies the forcing term needed to convert the unweighted weak flux identity into the weighted curvature–Gram identity.
--
--   **Original Lean conclusion excerpt**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Earlier hypotheses and the proof are omitted from this excerpt; the complete verified statement remains below.
--
--   ```lean
--       let Q := fun x i j => -hessianMatrix u x j i + ∑ a : Fin n,
--         (T x j i a * fderiv ℝ W (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ a) +
--           hessianMatrix u x i a * ∑ b : Fin n, hessianMatrix u x j b *
--             hessianMatrix W (gradient u x) b a)
--       ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), ∀ i j : Fin n,
--         Q x i j - (∑ a : Fin n, ∑ b : Fin n, T x i a b * D x j b a) +
--           (∑ b : Fin n, T x b i j * (∑ a : Fin n, D x a b a)) -
--           (∑ a : Fin n, J x i j a * fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ a)) =
--         -hessianMatrix u x i j +
--           (hessianMatrix u x * hessianMatrix W (gradient u x) * hessianMatrix u x) i j +
--           (R x * (Matrix.of fun a b => T x i a b) * R x *
--             (Matrix.of fun a b => T x j a b)).trace
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/IntegrationByParts/WeakHessianEvolution`](https://prove2.me/theorems/d20d941d-a690-4ebe-9a63-a346adf8dd16).
--
--   Definition modules: [`Analysis/BakryEmery/HessianOperator`](https://prove2.me/theorems/0a60d77a-9d99-47ed-a649-6e1a28e13392), [`Analysis/Operator/Coordinates`](https://prove2.me/theorems/104936bd-b536-4e43-8bdb-e45d2e66c788), [`Analysis/WeakDerivative/Basic`](https://prove2.me/theorems/5af72772-2fc4-48c4-926f-dd1d449f0f11).
--
--   Supporting theorems: [`ae_fderiv_mongeAmpere_exponent`](https://prove2.me/theorems/71049741-6710-4957-9e2a-2a505bfab529), [`ae_inverse_hessian_row_divergence_of_weak_derivative`](https://prove2.me/theorems/e773702c-7809-4847-beb6-e121927d46e0), [`ae_weak_third_derivative_symm`](https://prove2.me/theorems/236baf49-0092-428b-8c19-9934eff0cfd3).
--
--   Previous: [`integral_weak_hessian_flux_eq_trace_derivative`](https://prove2.me/theorems/6d0b46f6-29ee-4cf1-8e3f-098cb8c41989) · Next: [`integral_exp_neg_flux_of_unweighted`](https://prove2.me/theorems/ede33e09-7e75-4497-9ed6-66486b1825c1).
--
--   [Source excerpt, lines 1228–1239](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/WeakHessianEvolution.lean#L1228-L1239) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/WeakHessianEvolution.lean#L1198-L1280 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.WeakHessianEvolution`, declaration `_private.FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.WeakHessianEvolution.0.FunctionalInequalities.Analysis.ae_hessian_flux_forcing_minus_drift`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_WeakHessianEvolution

open Matrix MeasureTheory Set Filter
open FunctionalInequalities.Probability.Stein
set_option maxHeartbeats 1200000

theorem FunctionalInequalities.Analysis.ae_hessian_flux_forcing_minus_drift_readable {n : ℕ}
    {u W : EuclideanSpace ℝ (Fin n) → ℝ} {G LF : NNReal}
    (hu : ContDiff ℝ 1 u)
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
            ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
    let R := fun x => (hessianMatrix u x)⁻¹
    let D := fun x k b a => -((R x * (Matrix.of fun c d => T x k c d) * R x) b a)
    let J := fun x i j a => ∑ b : Fin n, R x b a * T x b i j
    let Q := fun x i j => -hessianMatrix u x j i + ∑ a : Fin n,
      (T x j i a * fderiv ℝ W (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ a) +
        hessianMatrix u x i a * ∑ b : Fin n, hessianMatrix u x j b *
          hessianMatrix W (gradient u x) b a)
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), ∀ i j : Fin n,
      Q x i j - (∑ a : Fin n, ∑ b : Fin n, T x i a b * D x j b a) +
        (∑ b : Fin n, T x b i j * (∑ a : Fin n, D x a b a)) -
        (∑ a : Fin n, J x i j a * fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ a)) =
      -hessianMatrix u x i j +
        (hessianMatrix u x * hessianMatrix W (gradient u x) * hessianMatrix u x) i j +
        (R x * (Matrix.of fun a b => T x i a b) * R x *
          (Matrix.of fun a b => T x j a b)).trace := by sorry
