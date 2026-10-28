-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_GaussianSmoothing_gaussian_product_source_stein_identity_readable
-- name    : FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussian_product_source_stein_identity_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:16:37.852997+00:00
-- url     : https://prove2.me/theorems/23d8691b-4721-4fa3-a71c-9a8a4ef02ab4
-- title:
--   Gaussian Product Source Stein Identity
-- statement:
--   This statement combines the affine source identity with the translated Gaussian identity on a product coupling.
--
--   Let $n\in\mathbb N$, let $u,h:\mathbb R^n\to\mathbb R$ be $C^1$, with $u$ and $∇u$ globally Lipschitz, and assume $\int e^{-u}=1$. Let $h$ be globally Lipschitz and bounded by $C$, let $S$ be continuous linear, let $v\in\mathbb R^n$, and let $s>0$. Define
--
--   $$
--   P=\bigl(\operatorname{volume}.\operatorname{tilted}(-u)\bigr)\otimes\gamma_s.
--   $$
--
--   Then the two displayed functions are integrable under $P$, and
--
--   $$
--   \begin{aligned}
--   &\int \langle S(∇u(y))+z,v\rangle h(S(∇u(y))+z)\,dP(y,z)\\
--   &=\int \left[\left\langle S^*v,\operatorname{action}\!\left(\nabla^2u(y),S^*∇h(S(∇u(y))+z)\right)\right\rangle
--   +(2s)^{-1}D_vh(S(∇u(y))+z)\right]dP(y,z).
--   \end{aligned}
--   $$
--
--   This is the exact product-coupling identity and includes all stated integrability conclusions.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave.GaussianSmoothing`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   set_option maxHeartbeats 800000 in
--   theorem gaussian_product_source_stein_identity {n : ℕ}
--       {u h : EuclideanSpace ℝ (Fin n) → ℝ} {L G Lh : NNReal}
--       (hu : ContDiff ℝ 1 u) (hL : LipschitzWith L u)
--       (hG : LipschitzWith G (gradient u))
--       (hnorm : (∫ y, Real.exp (-u y) ∂volume) = 1)
--       (hh : ContDiff ℝ 1 h) (hhLip : LipschitzWith Lh h)
--       (C : ℝ) (hbound : ∀ x, ‖h x‖ ≤ C)
--       (S : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
--       (v : EuclideanSpace ℝ (Fin n)) {s : ℝ} (hs : 0 < s) :
--       let P := ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).prod
--         (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw (V := EuclideanSpace ℝ (Fin n)) s)
--       Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
--         ⟪S (gradient u p.1) + p.2, v⟫ * h (S (gradient u p.1) + p.2)) P ∧
--       Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
--         ⟪S.adjoint v, action (hessianMatrix u p.1)
--           (S.adjoint (gradient h (S (gradient u p.1) + p.2)))⟫ +
--             (2 * s)⁻¹ * fderiv ℝ h (S (gradient u p.1) + p.2) v) P ∧
--       (∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
--         ⟪S (gradient u p.1) + p.2, v⟫ * h (S (gradient u p.1) + p.2) ∂P) =
--         ∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
--           ⟪S.adjoint v, action (hessianMatrix u p.1)
--             (S.adjoint (gradient h (S (gradient u p.1) + p.2)))⟫ +
--               (2 * s)⁻¹ * fderiv ℝ h (S (gradient u p.1) + p.2) v ∂P
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/Density/GaussianSmoothing/ProductCoupling`](https://prove2.me/theorems/ec60ae0c-90e6-43f3-859c-75d3c6dd9a5f).
--
--   Definition modules: [`Analysis/BakryEmery/HessianOperator`](https://prove2.me/theorems/0a60d77a-9d99-47ed-a649-6e1a28e13392), [`KLS/LogConcave/Density/GaussianSmoothing/Basic`](https://prove2.me/theorems/a2d7963c-80d1-434f-9795-020109b07575), [`Probability/Stein/Kernel`](https://prove2.me/theorems/6af08ed6-46c1-440c-8a8d-7c243989192e).
--
--   Supporting theorems: [`gaussianLaw_translated_directional_identity_of_bounded_lipschitz_test`](https://prove2.me/theorems/c0deab00-4b66-4ff2-9322-12a13e5f7645), [`gaussian_product_source_stein_pairings_integrable`](https://prove2.me/theorems/baf328a1-6649-44a0-8197-8f43bfab886c), [`source_affine_stein_identity_of_bounded_lipschitz_test`](https://prove2.me/theorems/e5b3ff9c-092e-463b-98ea-ed142c530c1b).
--
--   Previous: [`gaussian_product_source_stein_pairings_integrable`](https://prove2.me/theorems/baf328a1-6649-44a0-8197-8f43bfab886c) · Next: [`gaussian_product_compact_dual_bound`](https://prove2.me/theorems/c7109f6d-dfe4-4a98-a566-2c5d13265636).
--
--   [Source excerpt, lines 124–147](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/Density/GaussianSmoothing/ProductCoupling.lean#L124-L147) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/Density/GaussianSmoothing/ProductCoupling.lean#L124-L194 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.ProductCoupling`, declaration `FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussian_product_source_stein_identity`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_ProductCoupling

open MeasureTheory
open FunctionalInequalities.Probability.Stein
open scoped ContDiff RealInnerProductSpace Topology
set_option maxHeartbeats 800000

theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussian_product_source_stein_identity_readable {n : ℕ}
    {u h : EuclideanSpace ℝ (Fin n) → ℝ} {L G Lh : NNReal}
    (hu : ContDiff ℝ 1 u) (hL : LipschitzWith L u)
    (hG : LipschitzWith G (gradient u))
    (hnorm : (∫ y, Real.exp (-u y) ∂volume) = 1)
    (hh : ContDiff ℝ 1 h) (hhLip : LipschitzWith Lh h)
    (C : ℝ) (hbound : ∀ x, ‖h x‖ ≤ C)
    (S : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (v : EuclideanSpace ℝ (Fin n)) {s : ℝ} (hs : 0 < s) :
    let P := ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).prod
      (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw (V := EuclideanSpace ℝ (Fin n)) s)
    Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      ⟪S (gradient u p.1) + p.2, v⟫ * h (S (gradient u p.1) + p.2)) P ∧
    Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      ⟪S.adjoint v, action (hessianMatrix u p.1)
        (S.adjoint (gradient h (S (gradient u p.1) + p.2)))⟫ +
          (2 * s)⁻¹ * fderiv ℝ h (S (gradient u p.1) + p.2) v) P ∧
    (∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
      ⟪S (gradient u p.1) + p.2, v⟫ * h (S (gradient u p.1) + p.2) ∂P) =
      ∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
        ⟪S.adjoint v, action (hessianMatrix u p.1)
          (S.adjoint (gradient h (S (gradient u p.1) + p.2)))⟫ +
            (2 * s)⁻¹ * fderiv ℝ h (S (gradient u p.1) + p.2) v ∂P := by sorry
