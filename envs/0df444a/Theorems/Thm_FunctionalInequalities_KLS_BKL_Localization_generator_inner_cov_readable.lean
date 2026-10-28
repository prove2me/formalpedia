-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_generator_inner_cov_readable
-- name    : FunctionalInequalities.KLS.BKL.Localization.generator_inner_cov_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:14:30.917719+00:00
-- url     : https://prove2.me/theorems/e39e89cd-78e0-4dd6-b485-29a06311ff5b
-- title:
--   Covariance Operator Eigenfunction Identity
-- statement:
--   This formalizes the generator identity corresponding to BKL (69).
--
--   Let $n\in\mathbb N$, let $\mu$ be an isotropic compactly supported probability measure on `EuclideanSpace ℝ (Fin n)`, and let $p$ be a posterior parameter. For all $x,y\in\mathbb R^n$, the generator applied to the scalar covariance-operator coefficient satisfies
--
--   $$\mathcal L\left[q\mapsto\langle \operatorname{Cov}(\mu_q)x,y\rangle\right](p)
--   =-\langle\operatorname{Cov}(\mu_p)x,y\rangle.$$
--
--   Here `cov μ hc q` is the posterior covariance operator and `Localization.generator` is the uncut posterior generator. This identity is the operator-valued decay relation used in the covariance-generator analysis.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.BKL.Localization`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem generator_inner_cov (hiso : KLS.Isotropic μ) (p : Param n) (x y : EuclideanSpace ℝ (Fin n)) :
--       generator μ hc (fun q : Param n => ⟪cov μ hc q x, y⟫) p = -⟪cov μ hc p x, y⟫
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/Localization/CovarianceGenerator`](https://prove2.me/theorems/7af1dbcb-be0a-4bda-96c4-e0b07cecb1c1).
--
--   Definition modules: [`KLS/BKL/Localization/Coefficients`](https://prove2.me/theorems/d4044301-d978-4415-85b5-191b3ecf6f74), [`KLS/Isotropic`](https://prove2.me/theorems/b8da0fa3-d27f-46ae-b3b9-8c204df57e02).
--
--   Selected supporting theorems: [`inner_self_pos_of_comp_eq_id`](https://prove2.me/theorems/cd7bd662-8102-4f8b-ace4-e8e741d6c4ea), [`inner_self_pos_of_isPositive_of_isUnit`](https://prove2.me/theorems/8f74694a-1776-48f4-8eff-687b9d5a92eb), [`Covariance.inner_operator_self_pos_of_affineSupport_eq_top`](https://prove2.me/theorems/5af59f78-fcb6-4c1e-a63a-8d36d8da7f37), [`generator_posteriorExpectation`](https://prove2.me/theorems/e97e7cc4-ef35-4351-ba82-cfe8145edbfe), [`diffusionGenerator_mul`](https://prove2.me/theorems/2d42e13d-4529-4774-b00a-37bb995a10d9).
--
--   Previous: [`generator_posteriorExpectation`](https://prove2.me/theorems/e97e7cc4-ef35-4351-ba82-cfe8145edbfe).
--
--   [Source excerpt, lines 78–79](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Localization/CovarianceGenerator.lean#L78-L79) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Localization/CovarianceGenerator.lean#L77-L204 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Localization.CovarianceGenerator`, declaration `FunctionalInequalities.KLS.BKL.Localization.generator_inner_cov`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_CovarianceGenerator

open scoped RealInnerProductSpace ContDiff
variable {n : ℕ} (μ : MeasureTheory.ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).support)

theorem FunctionalInequalities.KLS.BKL.Localization.generator_inner_cov_readable (hiso : KLS.Isotropic μ) (p : Param n) (x y : EuclideanSpace ℝ (Fin n)) :
    generator μ hc (fun q : Param n => ⟪cov μ hc q x, y⟫) p = -⟪cov μ hc p x, y⟫ := by sorry
