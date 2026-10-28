-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_generator_hsNormSq_snd_readable
-- name    : FunctionalInequalities.KLS.BKL.Localization.generator_hsNormSq_snd_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:15:15.476871+00:00
-- url     : https://prove2.me/theorems/458648f7-5e6d-495f-af0b-3e5a75b3e463
-- title:
--   Generator of the Hilbert–Schmidt Norm of $Q$
-- statement:
--   This statement computes the localization generator applied to the squared Hilbert–Schmidt norm of the quadratic parameter, namely the identity described by $\mathcal L\|Q\|_{\mathrm{HS}}^2$.
--
--   Let $\mu$ be a compactly supported isotropic probability law on $\operatorname{EuclideanSpace}(\mathbb{R},\operatorname{Fin}n)$ and let $p=(c,Q)$ be a localization parameter. Then
--
--   $$
--   \operatorname{generator}\bigl(\mu,h_c,q\mapsto\|q_2\|_{\mathrm{HS}}^2\bigr)(p)
--   =2\sum_{j=1}^{n}
--   \left\langle Qe_j,\operatorname{cov}(\mu,p)^{-1}e_j\right\rangle.
--   $$
--
--   The formula has no diffusion contribution acting on $Q$ and is an exact generator-calculus identity.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.BKL.Localization`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem generator_hsNormSq_snd (hiso : KLS.Isotropic μ) (p : Param n) :
--       generator μ hc (fun q : Param n => hsNormSq q.2) p =
--         2 * ∑ j, ⟪p.2 (EuclideanSpace.basisFun (Fin n) ℝ j),
--           Ring.inverse (cov μ hc p) (EuclideanSpace.basisFun (Fin n) ℝ j)⟫
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/Localization/Lyapunov/Basic`](https://prove2.me/theorems/1ed793bf-4e2f-450b-b764-c2de2f762cf7).
--
--   Definition modules: [`KLS/BKL/Localization/Coefficients`](https://prove2.me/theorems/d4044301-d978-4415-85b5-191b3ecf6f74), [`KLS/Isotropic`](https://prove2.me/theorems/b8da0fa3-d27f-46ae-b3b9-8c204df57e02), [`Analysis/Operator/HilbertSchmidt`](https://prove2.me/theorems/06361c00-f2b7-428f-bab2-caf9f49e2f34).
--
--   Supporting theorems: [`inner_self_pos_of_isPositive_of_isUnit`](https://prove2.me/theorems/8f74694a-1776-48f4-8eff-687b9d5a92eb), [`Covariance.inner_operator_self_pos_of_affineSupport_eq_top`](https://prove2.me/theorems/5af59f78-fcb6-4c1e-a63a-8d36d8da7f37), [`fderiv_fderiv_fst_dir`](https://prove2.me/theorems/a0e8f301-14c9-4b9b-85b4-3ddfdb159789), [`sum_bilin_inverseSqrt_eq`](https://prove2.me/theorems/7f385f3c-593c-495c-ae8d-54a94b5ade43).
--
--   Previous: [`generator_norm_sq_fst`](https://prove2.me/theorems/fff7723a-0c09-4862-bd3f-d8025b08ca9d) · Next: [`fderiv_stdTrace_ringInverse_cov_noise`](https://prove2.me/theorems/428086ba-248f-46b6-b406-de56d14e5026).
--
--   [Source excerpt, lines 284–287](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Localization/Lyapunov/Basic.lean#L284-L287) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Localization/Lyapunov/Basic.lean#L282-L322 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Localization.Lyapunov.Basic`, declaration `FunctionalInequalities.KLS.BKL.Localization.generator_hsNormSq_snd`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Lyapunov_Basic

open scoped RealInnerProductSpace ContDiff
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Probability.Diffusion
variable {n : ℕ} (μ : MeasureTheory.ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).support)
set_option maxHeartbeats 1000000

theorem FunctionalInequalities.KLS.BKL.Localization.generator_hsNormSq_snd_readable (hiso : KLS.Isotropic μ) (p : Param n) :
    generator μ hc (fun q : Param n => hsNormSq q.2) p =
      2 * ∑ j, ⟪p.2 (EuclideanSpace.basisFun (Fin n) ℝ j),
        Ring.inverse (cov μ hc p) (EuclideanSpace.basisFun (Fin n) ℝ j)⟫ := by sorry
