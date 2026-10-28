-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_generator_posteriorExpectation_exp_inner_readable
-- name    : FunctionalInequalities.KLS.BKL.Localization.generator_posteriorExpectation_exp_inner_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:15:29.100001+00:00
-- url     : https://prove2.me/theorems/6a6bdaa6-0ece-4bfe-854e-2c005a8cead7
-- title:
--   Generator Cancellation for Posterior Exponential Expectations
-- statement:
--   This formalizes the generator cancellation for exponential posterior expectations.
--
--   Let $\mu$ be a compactly supported isotropic probability measure on $\mathbb{R}^n$, let $z\in\mathbb{R}^n$, and let $p$ be a localization parameter. For the function
--
--   $$
--   F(q)=\operatorname{posteriorExpectation}(\mu,q_1,q_2)\bigl[x\mapsto e^{\langle z,x\rangle}\bigr],
--   $$
--
--   one has
--
--   $$
--   \operatorname{generator}(\mu)(F)(p)=0.
--   $$
--
--   This is the joint-parameter form of the posterior cancellation identity used in the generator calculation for the log-Laplace transform.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.BKL.Localization`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem generator_posteriorExpectation_exp_inner (hiso : KLS.Isotropic μ)
--       (z : EuclideanSpace ℝ (Fin n)) (p : Param n) :
--       generator μ hc
--         (fun q : Param n => posteriorExpectation μ q.1 q.2 (fun x => Real.exp ⟪z, x⟫)) p = 0
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/Localization/LogLaplaceGenerator`](https://prove2.me/theorems/590f3074-6616-4d0a-abfd-f622c05acbcf).
--
--   Definition modules: [`KLS/BKL/Localization/Coefficients`](https://prove2.me/theorems/d4044301-d978-4415-85b5-191b3ecf6f74), [`Probability/Posterior/Generator`](https://prove2.me/theorems/f83f846f-96fd-4858-aa50-76e79f5d2363), [`KLS/Isotropic`](https://prove2.me/theorems/b8da0fa3-d27f-46ae-b3b9-8c204df57e02).
--
--   Selected supporting theorems: [`inner_self_pos_of_comp_eq_id`](https://prove2.me/theorems/cd7bd662-8102-4f8b-ace4-e8e741d6c4ea), [`inner_self_pos_of_isPositive_of_isUnit`](https://prove2.me/theorems/8f74694a-1776-48f4-8eff-687b9d5a92eb), [`Covariance.inner_operator_self_pos_of_affineSupport_eq_top`](https://prove2.me/theorems/5af59f78-fcb6-4c1e-a63a-8d36d8da7f37), [`fderiv_fderiv_fst_dir`](https://prove2.me/theorems/a0e8f301-14c9-4b9b-85b4-3ddfdb159789), [`sum_bilin_inverseSqrt_eq`](https://prove2.me/theorems/7f385f3c-593c-495c-ae8d-54a94b5ade43).
--
--   Previous: [`sum_inner_inverseSqrt_sq`](https://prove2.me/theorems/d2123cde-3328-49c8-bb38-74191da51e4b) · Next: [`posteriorExpectation_exp_inner_eq_exp`](https://prove2.me/theorems/66696a0d-fac3-4245-986c-d8e413dc01d5).
--
--   [Source excerpt, lines 220–223](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Localization/LogLaplaceGenerator.lean#L220-L223) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Localization/LogLaplaceGenerator.lean#L218-L235 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Localization.LogLaplaceGenerator`, declaration `FunctionalInequalities.KLS.BKL.Localization.generator_posteriorExpectation_exp_inner`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_LogLaplaceGenerator

open scoped RealInnerProductSpace
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Probability.Diffusion
variable {n : ℕ} (μ : MeasureTheory.ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).support)

theorem FunctionalInequalities.KLS.BKL.Localization.generator_posteriorExpectation_exp_inner_readable (hiso : KLS.Isotropic μ)
    (z : EuclideanSpace ℝ (Fin n)) (p : Param n) :
    generator μ hc
      (fun q : Param n => posteriorExpectation μ q.1 q.2 (fun x => Real.exp ⟪z, x⟫)) p = 0 := by sorry
