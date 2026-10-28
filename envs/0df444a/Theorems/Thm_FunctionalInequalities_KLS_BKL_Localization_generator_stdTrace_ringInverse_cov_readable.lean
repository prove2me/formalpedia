-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_generator_stdTrace_ringInverse_cov_readable
-- name    : FunctionalInequalities.KLS.BKL.Localization.generator_stdTrace_ringInverse_cov_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:15:03.860992+00:00
-- url     : https://prove2.me/theorems/8d08a995-5fda-4412-91ca-edf9a5b73120
-- title:
--   Generator of the Standard Trace of Inverse Covariance
-- statement:
--   This is an exact generator identity for the standard trace of the inverse posterior covariance.
--
--   Let $\mu$ be a probability measure on $\mathbb{R}^n\simeq\operatorname{EuclideanSpace}(\mathbb{R},\operatorname{Fin}(n))$ with compact support, and assume that $\mu$ is isotropic. For a localization parameter $p$, let $A(p)=\operatorname{cov}(\mu,p)$, let $H_k=D_cA(p)[\operatorname{noise}(\mu,p,k)]$, and let $S=A(p)^{-1/2}$. Then
--
--   $$
--   \mathcal L\!\left[\operatorname{tr}(A^{-1})\right](p)
--   =\operatorname{tr}(A(p)^{-1})
--   +\sum_k\sum_i
--   \left\|S\,H_k\,S\bigl(S e_i\bigr)\right\|^2,
--   $$
--
--   where the sums range over $k,i\in\operatorname{Fin}(n)$ and $e_i$ is the Euclidean coordinate basis. Here `generator`, `cov`, `stdTrace`, `inverseSqrt`, and `noise` are the formalized constructions.
--
--   This identity is the exact second-order calculus used to bound the Lyapunov generator in the localization argument.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.BKL.Localization`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem generator_stdTrace_ringInverse_cov (hiso : KLS.Isotropic μ) (p : Param n) :
--       generator μ hc (fun q : Param n => stdTrace (Ring.inverse (cov μ hc q))) p =
--         stdTrace (Ring.inverse (cov μ hc p)) +
--           ∑ k, ∑ i, ‖(inverseSqrt (cov μ hc p) * fderiv ℝ (cov μ hc) p (noise μ hc p k) * inverseSqrt (cov μ hc p))
--             (inverseSqrt (cov μ hc p) (EuclideanSpace.basisFun (Fin n) ℝ i))‖ ^ 2
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/Localization/Lyapunov/Basic`](https://prove2.me/theorems/1ed793bf-4e2f-450b-b764-c2de2f762cf7).
--
--   Definition modules: [`Analysis/Operator/HilbertSchmidt`](https://prove2.me/theorems/06361c00-f2b7-428f-bab2-caf9f49e2f34), [`KLS/BKL/Localization/Coefficients`](https://prove2.me/theorems/d4044301-d978-4415-85b5-191b3ecf6f74), [`KLS/Isotropic`](https://prove2.me/theorems/b8da0fa3-d27f-46ae-b3b9-8c204df57e02), [`Analysis/Operator/InverseSqrt`](https://prove2.me/theorems/2794bd57-af01-4015-a91a-cb7827d3a533).
--
--   Supporting theorems: [`inner_self_pos_of_isPositive_of_isUnit`](https://prove2.me/theorems/8f74694a-1776-48f4-8eff-687b9d5a92eb), [`Covariance.inner_operator_self_pos_of_affineSupport_eq_top`](https://prove2.me/theorems/5af59f78-fcb6-4c1e-a63a-8d36d8da7f37), [`generator_inner_cov`](https://prove2.me/theorems/e39e89cd-78e0-4dd6-b485-29a06311ff5b), [`vectorGenerator_clm_comp`](https://prove2.me/theorems/caa939ed-b8ae-4cc1-9991-797211b242e5), [`contDiff_posteriorCovariance_joint`](https://prove2.me/theorems/a52d87ad-7224-4ad7-973f-f486c36649d8).
--
--   Previous: [`fderiv_stdTrace_ringInverse_cov_noise`](https://prove2.me/theorems/428086ba-248f-46b6-b406-de56d14e5026).
--
--   [Source excerpt, lines 365–369](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Localization/Lyapunov/Basic.lean#L365-L369) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Localization/Lyapunov/Basic.lean#L363-L425 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Localization.Lyapunov.Basic`, declaration `FunctionalInequalities.KLS.BKL.Localization.generator_stdTrace_ringInverse_cov`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Lyapunov_Basic

open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Probability.Diffusion
variable {n : ℕ} (μ : MeasureTheory.ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).support)
set_option maxHeartbeats 1000000

theorem FunctionalInequalities.KLS.BKL.Localization.generator_stdTrace_ringInverse_cov_readable (hiso : KLS.Isotropic μ) (p : Param n) :
    generator μ hc (fun q : Param n => stdTrace (Ring.inverse (cov μ hc q))) p =
      stdTrace (Ring.inverse (cov μ hc p)) +
        ∑ k, ∑ i, ‖(inverseSqrt (cov μ hc p) * fderiv ℝ (cov μ hc) p (noise μ hc p k) * inverseSqrt (cov μ hc p))
          (inverseSqrt (cov μ hc p) (EuclideanSpace.basisFun (Fin n) ℝ i))‖ ^ 2 := by sorry
