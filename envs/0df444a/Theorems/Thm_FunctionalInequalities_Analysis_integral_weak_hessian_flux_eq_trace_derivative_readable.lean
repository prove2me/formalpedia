-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_integral_weak_hessian_flux_eq_trace_derivative_readable
-- name    : FunctionalInequalities.Analysis.integral_weak_hessian_flux_eq_trace_derivative_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:06:03.9589+00:00
-- url     : https://prove2.me/theorems/6d0b46f6-29ee-4cf1-8e3f-098cb8c41989
-- title:
--   Unweighted Weak Hessian Flux Identity
-- statement:
--   This formalizes part of Lemma 2.4 of Letwin (arXiv:2607.24164v1), as an unweighted weak flux identity.
--
--   Let $n\in\mathbb N$, $u:\mathbb R^n\to\mathbb R$ be $C^1$ with Lipschitz gradient, and let $T(x)_{kij}$ be a tensor. Assume that, for every coordinate $k$ and indices $i,j$, the component $(\nabla^2u)_{ij}$ has weak derivative $T_{kij}$ in the $k$-th basis direction, with $T_{kij}$ belonging locally to $L^2$ on every compact set. Assume similarly that the entries of $(\nabla^2u)^{-1}$ have weak derivatives
--   $$
--   -\bigl((\nabla^2u)^{-1}T_k(\nabla^2u)^{-1}\bigr)_{ij},
--   $$
--   that these derivatives are compact-locally in $L^2$, and that the inverse-Hessian entries are compact-locally in $L^\infty$ in the `ENNReal` sense. Finally, let $Q_{ij}$ be a tensor whose prescribed weak derivative is the trace of $(\nabla^2u)^{-1}T_i$ and whose components are compact-locally in $L^2$.
--
--   Define
--   $$
--   R=(\nabla^2u)^{-1},\qquad
--   D_{kba}=-(RT_kR)_{ba},\qquad
--   J_{ija}=\sum_bR_{ba}T_{bij},
--   $$
--   and
--   $$
--   C_{ij}=Q_{ij}-\sum_{a,b}T_{iab}D_{jba}
--   +\sum_bT_{bij}\sum_aD_{aba}.
--   $$
--   Then, for every $i,j\in\operatorname{Fin} n$, each $J_{ija}$ is compact-locally in $L^2$, $C_{ij}$ is locally integrable, and every compactly supported $C^1$ test function $\psi$ satisfies
--
--   $$
--   \int\sum_aJ_{ija}(x)\,\partial_a\psi(x)\,dx
--   =-\int C_{ij}(x)\psi(x)\,dx.
--   $$
--
--   The result is a technical weak integration-by-parts identity reusable by weighted Hessian evolution statements.
--
--   **Original Lean conclusion excerpt**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Earlier hypotheses and the proof are omitted from this excerpt; the complete verified statement remains below.
--
--   ```lean
--       ∀ i j : Fin n,
--         (∀ a : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
--           MemLp (fun x => J x i j a) 2
--             ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
--         LocallyIntegrable (fun x => C x i j)
--           (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
--         ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
--           ContDiff ℝ 1 ψ → HasCompactSupport ψ →
--           (∫ x, ∑ a : Fin n, J x i j a *
--             fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ a)
--             ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
--           -(∫ x, C x i j * ψ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/IntegrationByParts/WeakHessianEvolution`](https://prove2.me/theorems/d20d941d-a690-4ebe-9a63-a346adf8dd16).
--
--   Definition modules: [`Analysis/BakryEmery/HessianOperator`](https://prove2.me/theorems/0a60d77a-9d99-47ed-a649-6e1a28e13392), [`Analysis/Operator/Coordinates`](https://prove2.me/theorems/104936bd-b536-4e43-8bdb-e45d2e66c788), [`Analysis/WeakDerivative/Basic`](https://prove2.me/theorems/5af72772-2fc4-48c4-926f-dd1d449f0f11).
--
--   Supporting theorems: [`HasWeakDerivAlong.compact_mul_data`](https://prove2.me/theorems/14d1dc0b-7afe-403f-ae05-0178b771addc), [`ae_weak_third_derivative_symm`](https://prove2.me/theorems/236baf49-0092-428b-8c19-9934eff0cfd3), [`integral_weakDeriv_mul_eq_swap`](https://prove2.me/theorems/61cf322f-0c0f-4f7d-8765-ac88a842a6c5), [`localLp_hessian_flux_trace_forcing`](https://prove2.me/theorems/0d14ed2a-5f26-4feb-914f-b0d0e87bf35c), [`integral_array_pair_balance`](https://prove2.me/theorems/6a56d72a-b125-4b6e-9809-d8d6e98e7bf3).
--
--   Previous: [`integral_array_pair_balance`](https://prove2.me/theorems/6a56d72a-b125-4b6e-9809-d8d6e98e7bf3) · Next: [`ae_hessian_flux_forcing_minus_drift`](https://prove2.me/theorems/838d3785-b396-43ff-b452-a1eb6e64d796).
--
--   [Source excerpt, lines 918–929](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/WeakHessianEvolution.lean#L918-L929) · Frozen source `408915f`.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Lemma 2.4. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/WeakHessianEvolution.lean#L878-L1068 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.WeakHessianEvolution`, declaration `FunctionalInequalities.Analysis.integral_weak_hessian_flux_eq_trace_derivative`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_WeakHessianEvolution

open MeasureTheory Set Filter
open FunctionalInequalities.Probability.Stein
set_option maxHeartbeats 1200000

theorem FunctionalInequalities.Analysis.integral_weak_hessian_flux_eq_trace_derivative_readable {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {G : NNReal}
    (hu : ContDiff ℝ 1 u) (hG : LipschitzWith G (gradient u))
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
    (Q : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ)
    (hQ : ∀ i j : Fin n,
      HasWeakDerivAlong
        (fun x => ((hessianMatrix u x)⁻¹ * (Matrix.of fun a b => T x i a b)).trace)
        (fun x => Q x i j) (EuclideanSpace.basisFun (Fin n) ℝ j) ∧
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => Q x i j) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
    let R := fun x => (hessianMatrix u x)⁻¹
    let D := fun x k b a => -((R x * (Matrix.of fun c d => T x k c d) * R x) b a)
    let J := fun x i j a => ∑ b : Fin n, R x b a * T x b i j
    let C := fun x i j => Q x i j -
      (∑ a : Fin n, ∑ b : Fin n, T x i a b * D x j b a) +
      ∑ b : Fin n, T x b i j * (∑ a : Fin n, D x a b a)
    ∀ i j : Fin n,
      (∀ a : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => J x i j a) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      LocallyIntegrable (fun x => C x i j)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
        ContDiff ℝ 1 ψ → HasCompactSupport ψ →
        (∫ x, ∑ a : Fin n, J x i j a *
          fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ a)
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        -(∫ x, C x i j * ψ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by sorry
