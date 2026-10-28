-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_continuous_generator_of_contDiff_three_readable
-- name    : FunctionalInequalities.KLS.BKL.Localization.continuous_generator_of_contDiff_three_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:14:47.544084+00:00
-- url     : https://prove2.me/theorems/74acc94a-8282-4bc3-ae22-403b6ce74fcc
-- title:
--   Continuity of the Generator for $C^3$ Functions
-- statement:
--   This statement shows that the localization generator is continuous on every $C^3$ test function.
--
--   Let $\mu$ be a compactly supported isotropic probability law on $\operatorname{EuclideanSpace}(\mathbb{R},\operatorname{Fin}n)$. If $F$ on the localization parameter space satisfies
--
--   $$
--   F\in C^3,
--   $$
--
--   then the function $q\mapsto\operatorname{generator}(\mu,h_c,F)(q)$ is continuous:
--
--   $$
--   \operatorname{Continuous}(\operatorname{generator}(\mu,h_c,F)).
--   $$
--
--   The result is a regularity lemma for subsequent generator integration and comparison arguments.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.BKL.Localization`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem continuous_generator_of_contDiff_three (hiso : KLS.Isotropic μ) {F : Param n → ℝ}
--       (hF : ContDiff ℝ 3 F) : Continuous (generator μ hc F)
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/Localization/Energy/Regularity`](https://prove2.me/theorems/a5950f32-4ea5-4584-9d29-8056c7b809f6).
--
--   Definition modules: [`KLS/BKL/Localization/Coefficients`](https://prove2.me/theorems/d4044301-d978-4415-85b5-191b3ecf6f74), [`KLS/Isotropic`](https://prove2.me/theorems/b8da0fa3-d27f-46ae-b3b9-8c204df57e02).
--
--   Supporting theorems: [`Covariance.inner_operator_self_pos_of_affineSupport_eq_top`](https://prove2.me/theorems/5af59f78-fcb6-4c1e-a63a-8d36d8da7f37), [`locallyLipschitz_noise`](https://prove2.me/theorems/aa73acec-6bb4-4a4c-a7ca-0777d3c209ba), [`Isotropic.locallyLipschitz_inverseSqrt_covariance_joint`](https://prove2.me/theorems/315359b0-06f6-4b98-a4b9-2dc033ab5cf9), [`contDiff_posteriorCovariance_joint`](https://prove2.me/theorems/a52d87ad-7224-4ad7-973f-f486c36649d8), [`contDiff_posteriorMean_joint`](https://prove2.me/theorems/74843a12-a6a2-460d-9106-3e5347056aaa).
--
--   Previous: [`contDiff_cumulantEnergy_posterior`](https://prove2.me/theorems/0b698a15-4131-4b73-a00b-6eecdff79aa2).
--
--   [Source excerpt, lines 91–92](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Localization/Energy/Regularity.lean#L91-L92) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Localization/Energy/Regularity.lean#L90-L125 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Localization.Energy.Regularity`, declaration `FunctionalInequalities.KLS.BKL.Localization.continuous_generator_of_contDiff_three`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Energy_Regularity

variable {n : ℕ} (μ : MeasureTheory.ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).support)

theorem FunctionalInequalities.KLS.BKL.Localization.continuous_generator_of_contDiff_three_readable (hiso : KLS.Isotropic μ) {F : Param n → ℝ}
    (hF : ContDiff ℝ 3 F) : Continuous (generator μ hc F) := by sorry
