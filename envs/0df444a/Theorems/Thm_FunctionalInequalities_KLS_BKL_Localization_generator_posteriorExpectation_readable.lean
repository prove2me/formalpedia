-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_generator_posteriorExpectation_readable
-- name    : FunctionalInequalities.KLS.BKL.Localization.generator_posteriorExpectation_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:14:22.885802+00:00
-- url     : https://prove2.me/theorems/e97e7cc4-ef35-4351-ba82-cfe8145edbfe
-- title:
--   Zero Generator Drift for Posterior Expectations
-- statement:
--   This is the deterministic zero-drift identity associated with Equation (68) of Bizeul–Klartag–Lehec (arXiv:2610.05474v1).
--
--   Let $n\in\mathbb N$, let $\mu$ be an isotropic probability measure on `EuclideanSpace ℝ (Fin n)` with compact support, and let $f$ be measurable and bounded on the support: for some $C\ge0$, $\lVert f(x)\rVert\le C$. For every posterior parameter $p\in\operatorname{Param}(n)$, the uncut generator applied to the posterior expectation is zero:
--
--   $$\mathcal L\left[p\mapsto\int f\,d\mu_p\right]=0.$$
--
--   In Lean, the function is represented as `fun q => posteriorExpectation μ q.1 q.2 f`, and the generator is `Localization.generator`. The statement is finite-dimensional and concerns the deterministic generator identity only.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.BKL.Localization`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem generator_posteriorExpectation (hiso : KLS.Isotropic μ)
--       {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f) {C : ℝ} (hC : 0 ≤ C)
--       (hfb : ∀ x ∈ (μ : Measure (EuclideanSpace ℝ (Fin n))).support, ‖f x‖ ≤ C) (p : Param n) :
--       generator μ hc (fun q : Param n => posteriorExpectation μ q.1 q.2 f) p = 0
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/Localization/CovarianceGenerator`](https://prove2.me/theorems/7af1dbcb-be0a-4bda-96c4-e0b07cecb1c1).
--
--   Definition modules: [`KLS/BKL/Localization/Coefficients`](https://prove2.me/theorems/d4044301-d978-4415-85b5-191b3ecf6f74), [`Probability/Posterior/Generator`](https://prove2.me/theorems/f83f846f-96fd-4858-aa50-76e79f5d2363), [`KLS/Isotropic`](https://prove2.me/theorems/b8da0fa3-d27f-46ae-b3b9-8c204df57e02).
--
--   Selected supporting theorems: [`inner_self_pos_of_comp_eq_id`](https://prove2.me/theorems/cd7bd662-8102-4f8b-ace4-e8e741d6c4ea), [`inner_self_pos_of_isPositive_of_isUnit`](https://prove2.me/theorems/8f74694a-1776-48f4-8eff-687b9d5a92eb), [`Covariance.inner_operator_self_pos_of_affineSupport_eq_top`](https://prove2.me/theorems/5af59f78-fcb6-4c1e-a63a-8d36d8da7f37), [`fderiv_fderiv_fst_dir`](https://prove2.me/theorems/a0e8f301-14c9-4b9b-85b4-3ddfdb159789), [`sum_bilin_inverseSqrt_eq`](https://prove2.me/theorems/7f385f3c-593c-495c-ae8d-54a94b5ade43).
--
--   Next: [`generator_inner_cov`](https://prove2.me/theorems/e39e89cd-78e0-4dd6-b485-29a06311ff5b).
--
--   [Source excerpt, lines 61–64](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Localization/CovarianceGenerator.lean#L61-L64) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Localization/CovarianceGenerator.lean#L59-L75 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Localization.CovarianceGenerator`, declaration `FunctionalInequalities.KLS.BKL.Localization.generator_posteriorExpectation`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_CovarianceGenerator

open MeasureTheory ProbabilityTheory
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Probability.Diffusion
variable {n : ℕ} (μ : MeasureTheory.ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).support)

theorem FunctionalInequalities.KLS.BKL.Localization.generator_posteriorExpectation_readable (hiso : KLS.Isotropic μ)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f) {C : ℝ} (hC : 0 ≤ C)
    (hfb : ∀ x ∈ (μ : Measure (EuclideanSpace ℝ (Fin n))).support, ‖f x‖ ≤ C) (p : Param n) :
    generator μ hc (fun q : Param n => posteriorExpectation μ q.1 q.2 f) p = 0 := by sorry
