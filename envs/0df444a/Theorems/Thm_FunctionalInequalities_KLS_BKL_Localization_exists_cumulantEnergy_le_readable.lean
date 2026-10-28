-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_exists_cumulantEnergy_le_readable
-- name    : FunctionalInequalities.KLS.BKL.Localization.exists_cumulantEnergy_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:14:56.462255+00:00
-- url     : https://prove2.me/theorems/5481f760-ae1c-4c90-be25-67d353f6a39c
-- title:
--   A-Priori Posterior Cumulant Energy Bound
-- statement:
--   This statement gives an a-priori bound on posterior cumulant energies along the localization parameter space.
--
--   Let $\mu$ be a compactly supported isotropic log-concave probability law on $\operatorname{EuclideanSpace}(\mathbb{R},\operatorname{Fin}n)$. Let $r\ge0$ and assume
--
--   $$
--   \operatorname{supp}(\mu)\subseteq\overline{B}(0,r).
--   $$
--
--   For every $d\in\mathbb{N}$, there exists $C\ge0$ such that for every parameter $p=(c,Q)$ with $Q$ self-adjoint and positive semidefinite, and every $u$, the compact posterior satisfies
--
--   $$
--   \operatorname{cumulantEnergy}(\mu_{c,Q},d,u)
--   \le C\,\|u\|^2.
--   $$
--
--   The constant may depend on $\mu$, $r$, and $d$. This is a finite-dimensional posterior control statement used to justify integrability and localization estimates.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.BKL.Localization`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_cumulantEnergy_le (hiso : KLS.Isotropic μ) (hLC : KLS.LogConcave μ) {r : ℝ} (hr : 0 ≤ r)
--       (hsupp : (μ : Measure (EuclideanSpace ℝ (Fin n))).support ⊆ Metric.closedBall 0 r) (d : ℕ) :
--       ∃ C : ℝ, 0 ≤ C ∧ ∀ p : Param n, IsSelfAdjoint p.2 → (∀ x, 0 ≤ ⟪p.2 x, x⟫) →
--         ∀ u : EuclideanSpace ℝ (Fin n),
--           cumulantEnergy (compactPosterior μ hc p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n))) d u ≤ C * ‖u‖ ^ 2
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/Localization/Energy/Bound`](https://prove2.me/theorems/4ab05ed1-3d8d-48ff-a6a8-e41faa7f3068).
--
--   Definition modules: [`KLS/BKL/CumulantEnergy/Basic`](https://prove2.me/theorems/4f12a1ef-12d3-46f5-b544-7dda9d084086), [`KLS/BKL/Localization/Coefficients`](https://prove2.me/theorems/d4044301-d978-4415-85b5-191b3ecf6f74), [`Probability/LogConcave`](https://prove2.me/theorems/806cd3df-b03f-48fa-a2e4-4711229a309b), [`KLS/Isotropic`](https://prove2.me/theorems/b8da0fa3-d27f-46ae-b3b9-8c204df57e02), [`Probability/Posterior/CompactDomain`](https://prove2.me/theorems/38dd017c-ecae-4018-a0fd-eec5fa1b0dda).
--
--   Selected supporting theorems: [`tiltAverage_inner_eq_fderiv_logLaplace`](https://prove2.me/theorems/6e9a8c5a-1811-461e-b918-2514d0abe6ef), [`norm_posteriorMean_le`](https://prove2.me/theorems/1ba79c02-44ff-4be0-ac9c-b3cb262c225b), [`exists_sum_sq_cumulant_le_isotropic`](https://prove2.me/theorems/cfaadac6-0d48-4b92-9fe1-c1083e401bec), [`opNorm_covariance_compactPosterior_le_sq_radius`](https://prove2.me/theorems/becefc49-e2fe-406f-a71d-0f8f1d8fbe46), [`exists_uniform_norm_moments_tilted_quadraticExponent_of_compact`](https://prove2.me/theorems/840d9ee9-637c-4b2c-918e-01a3cf6f78a7).
--
--   Previous: [`norm_posteriorMean_le`](https://prove2.me/theorems/1ba79c02-44ff-4be0-ac9c-b3cb262c225b).
--
--   [Source excerpt, lines 193–197](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Localization/Energy/Bound.lean#L193-L197) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Localization/Energy/Bound.lean#L192-L256 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Localization.Energy.Bound`, declaration `FunctionalInequalities.KLS.BKL.Localization.exists_cumulantEnergy_le`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Energy_Bound

open MeasureTheory
open scoped RealInnerProductSpace ContDiff
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
variable {n : ℕ}
variable (μ : MeasureTheory.ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).support)

theorem FunctionalInequalities.KLS.BKL.Localization.exists_cumulantEnergy_le_readable (hiso : KLS.Isotropic μ) (hLC : KLS.LogConcave μ) {r : ℝ} (hr : 0 ≤ r)
    (hsupp : (μ : Measure (EuclideanSpace ℝ (Fin n))).support ⊆ Metric.closedBall 0 r) (d : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : Param n, IsSelfAdjoint p.2 → (∀ x, 0 ≤ ⟪p.2 x, x⟫) →
      ∀ u : EuclideanSpace ℝ (Fin n),
        cumulantEnergy (compactPosterior μ hc p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n))) d u ≤ C * ‖u‖ ^ 2 := by sorry
