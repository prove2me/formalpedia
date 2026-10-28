-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_GaussianSmoothing_gaussian_smoothed_quadratic_variance_le_latent_energy_readable
-- name    : FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussian_smoothed_quadratic_variance_le_latent_energy_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:17:20.848423+00:00
-- url     : https://prove2.me/theorems/b06bef5a-93db-4e5d-b4b0-013d668182b2
-- title:
--   Smoothed Quadratic Variance Bounded by Latent Product Energy
-- statement:
--   This is a finite-dimensional Gaussian-smoothing variance estimate.
--
--   Let $\mu$ be a probability measure on $E=\mathrm{EuclideanSpace}\,\mathbb R\,(\mathrm{Fin}\,n)$ such that `LogConcave μ` and whose affine support is the whole space. Let $u:E\to\mathbb R$ satisfy:
--
--   1. $u$ is $C^1$;
--   2. $u$ is globally Lipschitz with constant $L\in\mathbb{NNReal}$;
--   3. $\nabla u$ is globally Lipschitz with constant $G\in\mathbb{NNReal}$;
--   4. $\int_E e^{-u(y)}\,dy=1$;
--   5. the tilted Lebesgue measure with density proportional to $e^{-u}$, pushed forward by $\nabla u$, equals $\mu$.
--
--   Let $S:E\simeq E$ be a continuous linear equivalence, let $Q:E\to E$ be continuous linear and self-adjoint, and let $s>0$. Write $P=\bigl(e^{-u}\,dy\bigr)\otimes\gamma_s$, where $\gamma_s$ is the Gaussian law used by `gaussianLaw`, and let `smoothedLaw` denote the corresponding Gaussian-smoothed image law. Then
--
--   $$\operatorname{Var}_{\operatorname{smoothedLaw}(\mu\circ S^{-1},s)}\!\bigl(\langle Qx,x\rangle\bigr)
--   \le 4\sum_{i=1}^{n}\int_{E\times E}\left\|S\!\left(\operatorname{action}\!\left(\nabla^2u(p_1),S^*Qe_i\right)\right)+(2s)^{-1}Qe_i\right\|^2\,dP(p).$$
--
--   Here $e_i$ is the $i$th coordinate vector and the displayed right-hand side is exactly the latent product energy in the Lean statement. This provides a technical bridge from smoothed quadratic variance to Hessian-based latent energies.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave.GaussianSmoothing`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   set_option maxHeartbeats 1000000 in
--   theorem gaussian_smoothed_quadratic_variance_le_latent_energy {n : ℕ}
--       (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
--       (hLC : FunctionalInequalities.KLS.LogConcave μ)
--       (hfull : Probability.affineSupport μ = ⊤)
--       {u : EuclideanSpace ℝ (Fin n) → ℝ} {L G : NNReal}
--       (hu : ContDiff ℝ 1 u) (hL : LipschitzWith L u)
--       (hG : LipschitzWith G (gradient u))
--       (hnorm : (∫ y, Real.exp (-u y) ∂volume) = 1)
--       (hsource : ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map
--         (gradient u) = (μ : Measure (EuclideanSpace ℝ (Fin n))))
--       (S : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
--       (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
--       (hQ : IsSelfAdjoint Q) {s : ℝ} (hs : 0 < s) :
--       let P := ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).prod
--         (gaussianLaw (V := EuclideanSpace ℝ (Fin n)) s)
--       variance (fun x => ⟪Q x,x⟫) (smoothedLaw ((μ : Measure _).map S) s) ≤
--         4 * ∑ i : Fin n, ∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
--           ‖S (action (hessianMatrix u p.1) (S.toContinuousLinearMap.adjoint
--             (Q (EuclideanSpace.single i 1)))) + (2*s)⁻¹ • Q (EuclideanSpace.single i 1)‖ ^ 2 ∂P
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/Density/GaussianSmoothing/QuadraticVariance`](https://prove2.me/theorems/032e441a-7b5c-4cf8-9242-29a059b98a48).
--
--   Definition modules: [`Analysis/BakryEmery/HessianOperator`](https://prove2.me/theorems/0a60d77a-9d99-47ed-a649-6e1a28e13392), [`KLS/LogConcave/Density/GaussianSmoothing/Basic`](https://prove2.me/theorems/a2d7963c-80d1-434f-9795-020109b07575), [`Probability/LogConcave`](https://prove2.me/theorems/806cd3df-b03f-48fa-a2e4-4711229a309b), [`Probability/AffineSupport`](https://prove2.me/theorems/94abfb4a-13e9-434c-bb03-f6b05ced8e81), [`Probability/Stein/Kernel`](https://prove2.me/theorems/6af08ed6-46c1-440c-8a8d-7c243989192e).
--
--   Selected supporting theorems: [`gaussianLaw_exp_norm_integrable`](https://prove2.me/theorems/ec40927e-84c2-482a-84b6-84474bc6df0e), [`gaussian_product_compact_dual_bound`](https://prove2.me/theorems/c7109f6d-dfe4-4a98-a566-2c5d13265636), [`of_continuousLinearEquiv_map`](https://prove2.me/theorems/c637e7db-3431-42d0-bb61-ac5baf6882b0), [`variance_le_sum_of_partial_dual_bounds`](https://prove2.me/theorems/87d34084-ab4b-4b3e-96bf-c24d3921e663), [`Probability.affineSupport_mapContinuousLinearEquiv`](https://prove2.me/theorems/fde395de-3098-465b-b70c-cf883c0311a9).
--
--   [Source excerpt, lines 34–53](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/Density/GaussianSmoothing/QuadraticVariance.lean#L34-L53) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/Density/GaussianSmoothing/QuadraticVariance.lean#L34-L114 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.QuadraticVariance`, declaration `FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussian_smoothed_quadratic_variance_le_latent_energy`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_QuadraticVariance

open MeasureTheory Set ProbabilityTheory Filter
open FunctionalInequalities.Probability.Stein
open scoped ContDiff RealInnerProductSpace
set_option maxHeartbeats 1000000

theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussian_smoothed_quadratic_variance_le_latent_energy_readable {n : ℕ}
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hLC : FunctionalInequalities.KLS.LogConcave μ)
    (hfull : Probability.affineSupport μ = ⊤)
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {L G : NNReal}
    (hu : ContDiff ℝ 1 u) (hL : LipschitzWith L u)
    (hG : LipschitzWith G (gradient u))
    (hnorm : (∫ y, Real.exp (-u y) ∂volume) = 1)
    (hsource : ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map
      (gradient u) = (μ : Measure (EuclideanSpace ℝ (Fin n))))
    (S : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hQ : IsSelfAdjoint Q) {s : ℝ} (hs : 0 < s) :
    let P := ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).prod
      (gaussianLaw (V := EuclideanSpace ℝ (Fin n)) s)
    variance (fun x => ⟪Q x,x⟫) (smoothedLaw ((μ : Measure _).map S) s) ≤
      4 * ∑ i : Fin n, ∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
        ‖S (action (hessianMatrix u p.1) (S.toContinuousLinearMap.adjoint
          (Q (EuclideanSpace.single i 1)))) + (2*s)⁻¹ • Q (EuclideanSpace.single i 1)‖ ^ 2 ∂P := by sorry
