-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_exists_generator_lyapunov_le_readable
-- name    : FunctionalInequalities.KLS.BKL.Localization.exists_generator_lyapunov_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:15:32.345266+00:00
-- url     : https://prove2.me/theorems/97e70d80-18de-4ef1-846f-10a392703228
-- title:
--   Existence of a Lyapunov Generator Constant
-- statement:
--   This establishes a pointwise generator inequality for the localization Lyapunov function.
--
--   Let $\mu$ be a compactly supported isotropic log-concave probability measure on $\mathbb{R}^n$, assume `CumulantBoundCompact 2 8`, and suppose that for some $r\ge0$ the support of $\mu$ is contained in the closed ball $\overline B(0,r)$. Then there exists $K\ge0$ such that, for every localization parameter $p=(c,Q)$ with $Q$ self-adjoint and positive semidefinite,
--
--   $$
--   \mathcal L\,\operatorname{lyapunov}(p)
--   \le K\,\operatorname{lyapunov}(p).
--   $$
--
--   The formal statement asserts existence of $K$ and does not require a dimension-free choice. It packages the generator estimates for the separate components of `lyapunov`.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.BKL.Localization`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   set_option maxHeartbeats 1000000 in
--   theorem exists_generator_lyapunov_le (hiso : KLS.Isotropic μ) (hLC : KLS.LogConcave μ)
--       (h8 : LogConcave.Suspension.CumulantBoundCompact 2 8) {r : ℝ} (hr : 0 ≤ r)
--       (hsupp : (μ : Measure (EuclideanSpace ℝ (Fin n))).support ⊆ Metric.closedBall 0 r) :
--       ∃ K : ℝ, 0 ≤ K ∧ ∀ p : Param n, IsSelfAdjoint p.2 → (∀ x, 0 ≤ ⟪p.2 x, x⟫) →
--         generator μ hc (lyapunov μ hc) p ≤ K * lyapunov μ hc p
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/Localization/Lyapunov/Bound`](https://prove2.me/theorems/aa56646a-429f-4f7a-b76b-db51e21f5aa2).
--
--   Definition modules: [`KLS/BKL/Localization/Coefficients`](https://prove2.me/theorems/d4044301-d978-4415-85b5-191b3ecf6f74), [`Probability/LogConcave`](https://prove2.me/theorems/806cd3df-b03f-48fa-a2e4-4711229a309b), [`KLS/Isotropic`](https://prove2.me/theorems/b8da0fa3-d27f-46ae-b3b9-8c204df57e02), [`KLS/BKL/Localization/Lyapunov/Basic`](https://prove2.me/theorems/1ed793bf-4e2f-450b-b764-c2de2f762cf7), [`KLS/BKL/CompactReduction`](https://prove2.me/theorems/a4e51f37-ee65-417d-a309-c9c31bff2101).
--
--   Selected supporting theorems: [`inner_self_pos_of_comp_eq_id`](https://prove2.me/theorems/cd7bd662-8102-4f8b-ace4-e8e741d6c4ea), [`opNorm_sq_le_hsNormSq`](https://prove2.me/theorems/4e1eeade-d7a1-4e5a-8b0a-e8fcba8ae762), [`sum_inner_apply_le_sqrt_hsNormSq_mul`](https://prove2.me/theorems/9a0d0118-09fb-42ba-8956-a35ad70bd1c0), [`Covariance.inner_operator_self_pos_of_affineSupport_eq_top`](https://prove2.me/theorems/5af59f78-fcb6-4c1e-a63a-8d36d8da7f37), [`generator_hsNormSq_snd`](https://prove2.me/theorems/458648f7-5e6d-495f-af0b-3e5a75b3e463).
--
--   Previous: [`sum_sq_fderiv_stdTrace_ringInverse_cov_noise_le`](https://prove2.me/theorems/b5070c35-02cf-4bfa-a4a7-cf8eb07675cc).
--
--   [Source excerpt, lines 379–384](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Localization/Lyapunov/Bound.lean#L379-L384) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Localization/Lyapunov/Bound.lean#L379-L622 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Localization.Lyapunov.Bound`, declaration `FunctionalInequalities.KLS.BKL.Localization.exists_generator_lyapunov_le`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Lyapunov_Bound

open MeasureTheory
open scoped RealInnerProductSpace ContDiff
variable {n : ℕ} (μ : MeasureTheory.ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).support)
set_option maxHeartbeats 1000000

theorem FunctionalInequalities.KLS.BKL.Localization.exists_generator_lyapunov_le_readable (hiso : KLS.Isotropic μ) (hLC : KLS.LogConcave μ)
    (h8 : LogConcave.Suspension.CumulantBoundCompact 2 8) {r : ℝ} (hr : 0 ≤ r)
    (hsupp : (μ : Measure (EuclideanSpace ℝ (Fin n))).support ⊆ Metric.closedBall 0 r) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ p : Param n, IsSelfAdjoint p.2 → (∀ x, 0 ≤ ⟪p.2 x, x⟫) →
      generator μ hc (lyapunov μ hc) p ≤ K * lyapunov μ hc p := by sorry
