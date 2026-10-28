-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_generator_cumulant_posterior_readable
-- name    : FunctionalInequalities.KLS.BKL.Localization.generator_cumulant_posterior_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:15:24.900159+00:00
-- url     : https://prove2.me/theorems/a8578c33-036f-4c18-b2db-a9b7abd9284e
-- title:
--   Posterior Cumulant Generator Identity
-- statement:
--   This formalizes the generator form of BKL Lemma 4.3, equation (73), cited at p. 20 of Bizeul–Klartag–Lehec (arXiv:2610.05474v1).
--
--   Let $\mu$ be an isotropic probability measure on $\mathrm{EuclideanSpace}\,\mathbb R\,(\mathrm{Fin}\,n)$ with compact support. Let $m\in\mathbb N$ satisfy $3\le m$, let $h:\mathrm{Fin}(m)\to\mathrm{EuclideanSpace}\,\mathbb R\,(\mathrm{Fin}\,n)$ be a family of directions, let $i_0\in\mathrm{Fin}(m)$, and let $p$ be a localization parameter. For each parameter $q$, evaluate the $m$th cumulant of the compact posterior at $q$ on $h$.
--
--   Then
--
--   $$
--   \mathcal L_p\bigl[\kappa_m(\mu_p)(h)\bigr]
--   =-\left(m\,\kappa_m(\mu_p)(h)+L_m(\mu_p)(h,i_0)\right),
--   $$
--
--   where `lowerDrift` is the middle-term contribution at slot $i_0$. The theorem is an auxiliary pointwise identity for posterior cumulants and is used in generator-based energy estimates.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.BKL.Localization`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem generator_cumulant_posterior (hiso : KLS.Isotropic μ) {m : ℕ} (hm : 3 ≤ m)
--       (h : Fin m → EuclideanSpace ℝ (Fin n)) (i₀ : Fin m) (p : Param n) :
--       generator μ hc
--           (fun q : Param n => cumulant (compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n))) m h) p =
--         -((m : ℝ) * cumulant (compactPosterior μ hc p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n))) m h +
--           lowerDrift (compactPosterior μ hc p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n))) h i₀)
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/Localization/CumulantGenerator`](https://prove2.me/theorems/f937fdfc-a22d-4fdf-a9aa-a094d34ecbc2).
--
--   Definition modules: [`KLS/BKL/Localization/Coefficients`](https://prove2.me/theorems/d4044301-d978-4415-85b5-191b3ecf6f74), [`KLS/Isotropic`](https://prove2.me/theorems/b8da0fa3-d27f-46ae-b3b9-8c204df57e02), [`KLS/BKL/CumulantEnergy/Basic`](https://prove2.me/theorems/4f12a1ef-12d3-46f5-b544-7dda9d084086), [`Analysis/BakryEmery/Cumulant/Basic`](https://prove2.me/theorems/c2d5b99d-f2d1-47d4-a2c5-2cf685ca2598), [`Probability/Posterior/CompactDomain`](https://prove2.me/theorems/38dd017c-ecae-4018-a0fd-eec5fa1b0dda).
--
--   Selected supporting theorems: [`iteratedFDeriv_inner_centeredGradient_zero_grouped_of_compact`](https://prove2.me/theorems/6ef0164c-f2a7-4cf0-81c8-23be29e9ee22), [`Covariance.inner_operator_self_pos_of_affineSupport_eq_top`](https://prove2.me/theorems/5af59f78-fcb6-4c1e-a63a-8d36d8da7f37), [`generator_logLaplace_posterior`](https://prove2.me/theorems/d04c501c-dd44-4e05-9714-2e8906ff495e), [`contDiff_logPartition_joint`](https://prove2.me/theorems/4f6af24d-bf34-47a4-ab0b-b8f6855e12d6), [`fderiv_logPartition_c_apply`](https://prove2.me/theorems/d56dc845-a2d9-42d9-b22a-bbd6ef8df04f).
--
--   [Source excerpt, lines 225–230](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Localization/CumulantGenerator.lean#L225-L230) · Frozen source `408915f`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Lemma 4.3, p. 20. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Localization/CumulantGenerator.lean#L221-L323 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Localization.CumulantGenerator`, declaration `FunctionalInequalities.KLS.BKL.Localization.generator_cumulant_posterior`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_CumulantGenerator

open MeasureTheory
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Probability.Diffusion
variable {n : ℕ} (μ : MeasureTheory.ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).support)
set_option maxHeartbeats 2000000

theorem FunctionalInequalities.KLS.BKL.Localization.generator_cumulant_posterior_readable (hiso : KLS.Isotropic μ) {m : ℕ} (hm : 3 ≤ m)
    (h : Fin m → EuclideanSpace ℝ (Fin n)) (i₀ : Fin m) (p : Param n) :
    generator μ hc
        (fun q : Param n => cumulant (compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n))) m h) p =
      -((m : ℝ) * cumulant (compactPosterior μ hc p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n))) m h +
        lowerDrift (compactPosterior μ hc p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n))) h i₀) := by sorry
