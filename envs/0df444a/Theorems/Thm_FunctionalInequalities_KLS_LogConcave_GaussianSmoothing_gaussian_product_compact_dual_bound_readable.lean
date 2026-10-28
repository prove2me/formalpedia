-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_GaussianSmoothing_gaussian_product_compact_dual_bound_readable
-- name    : FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussian_product_compact_dual_bound_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:16:47.35692+00:00
-- url     : https://prove2.me/theorems/c7109f6d-dfe4-4a98-a566-2c5d13265636
-- title:
--   Gaussian Product Compact Dual Bound
-- statement:
--   This is a technical compact-test estimate for a Gaussian product coupling in finite-dimensional Euclidean space.
--
--   Let $n\in\mathbb N$, let $\mu$ and $\nu$ be probability measures on $E=\operatorname{EuclideanSpace}(\mathbb R,\operatorname{Fin}(n))$, and let $u:E\to\mathbb R$ and $L,G\in[0,\infty)$ satisfy:
--
--   1. $u$ is $C^1$.
--   2. $u$ is $L$-Lipschitz.
--   3. $\nabla u$ is $G$-Lipschitz.
--   4. $\int_E e^{-u(y)}\,dy=1$.
--   5. The pushforward of the tilted volume measure $e^{-u}\,dy$ by $\nabla u$ is $\mu$.
--
--   For every continuous linear map $S:E\to E$, vector $v\in E$, scalar $s>0$ such that $\nu$ is the $s$-Gaussian smoothing of the pushforward $S_\#\mu$, and every $C^\infty$ compactly supported function $h:E\to\mathbb R$, one has
--
--   $$
--   \left(\int_E \langle x,v\rangle h(x)\,d\nu(x)\right)^2
--   \le
--   \left(\int_{E\times E}
--   \left\|S\!\left(\operatorname{action}(\nabla^2u(p_1),S^*v)\right)+(2s)^{-1}v\right\|^2\,dP(p_1,p_2)\right)
--   \left(\int_E \|Df(x)\|^2\,d\nu(x)\right),
--   $$
--
--   where $P$ is the product of the tilted source measure and the Gaussian law of variance parameter $s$. Here the derivative term is the operator norm of the Fréchet derivative $Dh$ (written in Lean as `fderiv ℝ h x`). The statement is reusable as a compact dual Cauchy–Schwarz estimate for this particular latent Gaussian coupling; it does not construct a target Stein kernel or an inverse transport.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave.GaussianSmoothing`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   set_option maxHeartbeats 800000 in
--   theorem gaussian_product_compact_dual_bound {n : ℕ}
--       (μ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
--       {u : EuclideanSpace ℝ (Fin n) → ℝ} {L G : NNReal}
--       (hu : ContDiff ℝ 1 u) (hL : LipschitzWith L u)
--       (hG : LipschitzWith G (gradient u))
--       (hnorm : (∫ y, Real.exp (-u y) ∂volume) = 1)
--       (hsource : ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map
--         (gradient u) = (μ : Measure (EuclideanSpace ℝ (Fin n))))
--       (S : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
--       (v : EuclideanSpace ℝ (Fin n)) {s : ℝ} (hs : 0 < s)
--       (hν : (ν : Measure (EuclideanSpace ℝ (Fin n))) = smoothedLaw ((μ : Measure _).map S) s)
--       (h : EuclideanSpace ℝ (Fin n) → ℝ) (hh : ContDiff ℝ ∞ h) (hhc : HasCompactSupport h) :
--       let P := ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).prod
--         (gaussianLaw (V := EuclideanSpace ℝ (Fin n)) s)
--       (∫ x, ⟪x,v⟫ * h x ∂(ν : Measure _)) ^ 2 ≤
--         (∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
--           ‖S (action (hessianMatrix u p.1) (S.adjoint v)) + (2*s)⁻¹ • v‖ ^ 2 ∂P) *
--         ∫ x, ‖fderiv ℝ h x‖ ^ 2 ∂(ν : Measure _)
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/Density/GaussianSmoothing/ProductCoupling`](https://prove2.me/theorems/ec60ae0c-90e6-43f3-859c-75d3c6dd9a5f).
--
--   Definition modules: [`Analysis/BakryEmery/HessianOperator`](https://prove2.me/theorems/0a60d77a-9d99-47ed-a649-6e1a28e13392), [`KLS/LogConcave/Density/GaussianSmoothing/Basic`](https://prove2.me/theorems/a2d7963c-80d1-434f-9795-020109b07575), [`Probability/Stein/Kernel`](https://prove2.me/theorems/6af08ed6-46c1-440c-8a8d-7c243989192e).
--
--   Supporting theorems: [`gaussian_product_latent_map`](https://prove2.me/theorems/3d05d9ff-f20e-4259-8e76-31eb720af291), [`gaussian_product_source_stein_identity`](https://prove2.me/theorems/23d8691b-4721-4fa3-a71c-9a8a4ef02ab4), [`gaussian_product_source_stein_pairings_integrable`](https://prove2.me/theorems/baf328a1-6649-44a0-8197-8f43bfab886c), [`compact_linear_pairing_sq_le_of_source_identity`](https://prove2.me/theorems/e6796e12-15fb-4572-92b1-4ade1d18cdc8).
--
--   Previous: [`gaussian_product_source_stein_identity`](https://prove2.me/theorems/23d8691b-4721-4fa3-a71c-9a8a4ef02ab4).
--
--   [Source excerpt, lines 208–226](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/Density/GaussianSmoothing/ProductCoupling.lean#L208-L226) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/Density/GaussianSmoothing/ProductCoupling.lean#L208-L276 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.ProductCoupling`, declaration `FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussian_product_compact_dual_bound`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_ProductCoupling

open MeasureTheory
open FunctionalInequalities.Probability.Stein
open scoped ContDiff RealInnerProductSpace
set_option maxHeartbeats 800000

theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussian_product_compact_dual_bound_readable {n : ℕ}
    (μ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {L G : NNReal}
    (hu : ContDiff ℝ 1 u) (hL : LipschitzWith L u)
    (hG : LipschitzWith G (gradient u))
    (hnorm : (∫ y, Real.exp (-u y) ∂volume) = 1)
    (hsource : ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map
      (gradient u) = (μ : Measure (EuclideanSpace ℝ (Fin n))))
    (S : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (v : EuclideanSpace ℝ (Fin n)) {s : ℝ} (hs : 0 < s)
    (hν : (ν : Measure (EuclideanSpace ℝ (Fin n))) = smoothedLaw ((μ : Measure _).map S) s)
    (h : EuclideanSpace ℝ (Fin n) → ℝ) (hh : ContDiff ℝ ∞ h) (hhc : HasCompactSupport h) :
    let P := ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).prod
      (gaussianLaw (V := EuclideanSpace ℝ (Fin n)) s)
    (∫ x, ⟪x,v⟫ * h x ∂(ν : Measure _)) ^ 2 ≤
      (∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
        ‖S (action (hessianMatrix u p.1) (S.adjoint v)) + (2*s)⁻¹ • v‖ ^ 2 ∂P) *
      ∫ x, ‖fderiv ℝ h x‖ ^ 2 ∂(ν : Measure _) := by sorry
