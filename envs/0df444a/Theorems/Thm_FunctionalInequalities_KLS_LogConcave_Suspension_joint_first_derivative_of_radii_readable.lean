-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_joint_first_derivative_of_radii_readable
-- name    : FunctionalInequalities.KLS.LogConcave.Suspension.joint_first_derivative_of_radii_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:19:27.751826+00:00
-- url     : https://prove2.me/theorems/36ffa587-610d-4253-bdcc-464589c23e0b
-- title:
--   Joint Scalar-Direction Derivative Under Explicit Exponential-Moment Radii
-- statement:
--   This auxiliary lemma states the scalar-direction derivative of the joint logarithmic Laplace transform under explicit local moment assumptions.
--
--   Let $n,N\in\mathbb N$ with $N>0$, $E=\mathbb R^n$ (`EuclideanSpace ℝ (Fin n)`), $\mu$ a probability measure on $E$, and $f:E\to\mathbb R$ measurable. Let $\beta,r_J,r_G>0$, $\sigma_\beta=\sqrt{1+2/\beta^2}$ (`sigma`), and $\lambda=$ `jointLaw` $\mu\ f\ \beta\ \sigma_\beta\ N$ on $H=$ `JointSpace` $N\ n$. Let $\Gamma$ be the graph law of $(f(x),x)$ in the Euclidean space indexed by $\operatorname{Option}(\operatorname{Fin}n)$ (`Measure.map`). Assume:
--   1. $e^{r_J\|p\|}\in L^1(\lambda)$.
--   2. $e^{r_G\|y\|}\in L^1(\Gamma)$.
--
--   For $z\in H$ with scalar coordinate $z_0=0$ and $\|z\|<\min(r_J,r_G)$, write $z_i\in E$ for its copy blocks and $e_0$ for the scalar coordinate unit vector. Then
--   $$
--   \left.\frac{d}{dw}\right|_{w=0}\Lambda_\lambda(we_0+z)
--   =\frac{\sum_{i\in\operatorname{Fin}N}F_f(z_i)}{\sigma_\beta\sqrt N}.
--   $$
--
--   Here $\Lambda_\lambda=$ `logLaplace` and $F_f=$ `tiltAverage`, the average of $f$ under the exponential tilt at its argument. The conclusion is `HasDerivAt`, including derivative existence. This local identity requires no regular-potential or isotropy hypothesis.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave.Suspension`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   private theorem joint_first_derivative_of_radii {n N : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n)))
--       [IsProbabilityMeasure μ] {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f)
--       {β rJ rG : ℝ} (hβ : 0 < β) (hN : 0 < N) (_hrJ : 0 < rJ) (hrG : 0 < rG)
--       (hjoint : Integrable (fun p : JointSpace N n => Real.exp (rJ * ‖p‖))
--         (jointLaw μ f β (sigma β) N))
--       (hgraph : Integrable (fun y : EuclideanSpace ℝ (Option (Fin n)) => Real.exp (rG * ‖y‖))
--         (μ.map (fun x : EuclideanSpace ℝ (Fin n) =>
--           (WithLp.toLp 2 fun o => Option.elim o (f x) fun j => x j :
--             EuclideanSpace ℝ (Option (Fin n))))))
--       (z : JointSpace N n) (hzero : z none = 0) (hz : ‖z‖ < min rJ rG) :
--       HasDerivAt (fun w : ℝ => logLaplace (jointLaw μ f β (sigma β) N)
--           (w • EuclideanSpace.basisFun (Option (Fin N × Fin n)) ℝ none + z))
--         ((∑ i : Fin N, tiltAverage μ f
--           (WithLp.toLp 2 fun j => z (some (i, j)))) / (sigma β * Real.sqrt N)) 0
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/Suspension/Derivatives`](https://prove2.me/theorems/3fa39843-9f8d-446f-806f-25b47f8ada2b).
--
--   Definition modules: [`Analysis/BakryEmery/Cumulant/Basic`](https://prove2.me/theorems/c2d5b99d-f2d1-47d4-a2c5-2cf685ca2598), [`KLS/BKL/Suspension/Law`](https://prove2.me/theorems/3aa21ca1-97e4-4f56-86c5-3a01d28b38f3), [`Analysis/BakryEmery/Tilt/Basic`](https://prove2.me/theorems/5a944547-1394-433f-9c0c-8efcf1f0d48a).
--
--   Supporting theorems: [`logLaplace_jointLaw_factorization`](https://prove2.me/theorems/d7decbed-2d29-44e0-9116-1fd9deec5adb), [`laplaceMeasure_mgf`](https://prove2.me/theorems/e6314ac4-2242-4f95-90fa-1ef8e685bab6), [`graph_log_integral_hasDerivAt_zero`](https://prove2.me/theorems/33019b04-662c-4c4b-b629-8d98f5f8344d).
--
--   Previous: [`graph_log_integral_hasDerivAt_zero`](https://prove2.me/theorems/33019b04-662c-4c4b-b629-8d98f5f8344d) · Next: [`fderiv_logLaplace_jointLaw_none`](https://prove2.me/theorems/c111409b-45db-45b0-903a-b9f1a6b86e12).
--
--   [Source excerpt, lines 255–268](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Suspension/Derivatives.lean#L255-L268) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Suspension/Derivatives.lean#L254-L309 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Suspension.Derivatives`, declaration `_private.FunctionalInequalities.KLS.BKL.Suspension.Derivatives.0.FunctionalInequalities.KLS.LogConcave.Suspension.joint_first_derivative_of_radii`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Suspension_Derivatives

open MeasureTheory FunctionalInequalities FunctionalInequalities.Analysis.BakryEmery

theorem FunctionalInequalities.KLS.LogConcave.Suspension.joint_first_derivative_of_radii_readable {n N : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure μ] {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f)
    {β rJ rG : ℝ} (hβ : 0 < β) (hN : 0 < N) (_hrJ : 0 < rJ) (hrG : 0 < rG)
    (hjoint : Integrable (fun p : JointSpace N n => Real.exp (rJ * ‖p‖))
      (jointLaw μ f β (sigma β) N))
    (hgraph : Integrable (fun y : EuclideanSpace ℝ (Option (Fin n)) => Real.exp (rG * ‖y‖))
      (μ.map (fun x : EuclideanSpace ℝ (Fin n) =>
        (WithLp.toLp 2 fun o => Option.elim o (f x) fun j => x j :
          EuclideanSpace ℝ (Option (Fin n))))))
    (z : JointSpace N n) (hzero : z none = 0) (hz : ‖z‖ < min rJ rG) :
    HasDerivAt (fun w : ℝ => logLaplace (jointLaw μ f β (sigma β) N)
        (w • EuclideanSpace.basisFun (Option (Fin N × Fin n)) ℝ none + z))
      ((∑ i : Fin N, tiltAverage μ f
        (WithLp.toLp 2 fun j => z (some (i, j)))) / (sigma β * Real.sqrt N)) 0 := by sorry
