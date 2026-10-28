-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_contDiff_cumulant_posterior_readable
-- name    : FunctionalInequalities.KLS.BKL.Localization.contDiff_cumulant_posterior_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:14:34.682025+00:00
-- url     : https://prove2.me/theorems/fae38448-b47c-4a2d-b61a-67ba2745ecc0
-- title:
--   Joint Smoothness of Posterior Cumulants
-- statement:
--   This statement records the joint smoothness of posterior cumulants in the parameter pair $p=(c,Q)$ for compactly supported priors.
--
--   Let $\mu$ be a probability law on $\operatorname{EuclideanSpace}(\mathbb{R},\operatorname{Fin}n)$ with compact support. Let $m\ge1$ and let $h:\operatorname{Fin}m\to\operatorname{EuclideanSpace}(\mathbb{R},\operatorname{Fin}n)$. Then
--
--   $$
--    p\longmapsto \kappa_m(\mu_{p_1,p_2})(h)
--   $$
--
--   is $C^\infty$ on the full parameter space:
--
--   $$
--   \operatorname{ContDiff}(\mathbb{R},\infty,p\mapsto
--   \operatorname{cumulant}(\mu_{p_1,p_2},m)(h)).
--   $$
--
--   This regularity result supports differentiation of cumulant-valued quantities along the localization parameter space.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.BKL.Localization`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem contDiff_cumulant_posterior {m : ℕ} (hm : 1 ≤ m) (h : Fin m → EuclideanSpace ℝ (Fin n)) :
--       ContDiff ℝ ∞ (fun q : Param n =>
--         cumulant (compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n))) m h)
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/Localization/CumulantDerivative`](https://prove2.me/theorems/b075fb8a-3376-43d8-a3ac-d3bc2b12f9f8).
--
--   Definition modules: [`KLS/BKL/Localization/Coefficients`](https://prove2.me/theorems/d4044301-d978-4415-85b5-191b3ecf6f74), [`Analysis/BakryEmery/Cumulant/Basic`](https://prove2.me/theorems/c2d5b99d-f2d1-47d4-a2c5-2cf685ca2598), [`Probability/Posterior/CompactDomain`](https://prove2.me/theorems/38dd017c-ecae-4018-a0fd-eec5fa1b0dda).
--
--   Supporting theorems: [`contDiff_logPartition_joint`](https://prove2.me/theorems/4f6af24d-bf34-47a4-ab0b-b8f6855e12d6), [`cumulant_compactPosterior`](https://prove2.me/theorems/be65aff1-f18a-49ae-a8b8-b2bf0b7da5d2).
--
--   Next: [`fderiv_cumulant_posterior_apply`](https://prove2.me/theorems/7e33f35a-71f2-43a6-bb75-a119f0e67849).
--
--   [Source excerpt, lines 93–95](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Localization/CumulantDerivative.lean#L93-L95) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Localization/CumulantDerivative.lean#L90-L124 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Localization.CumulantDerivative`, declaration `FunctionalInequalities.KLS.BKL.Localization.contDiff_cumulant_posterior`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_CumulantDerivative

open MeasureTheory
open scoped RealInnerProductSpace ContDiff
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Analysis.BakryEmery
variable {n : ℕ} (μ : MeasureTheory.ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).support)

theorem FunctionalInequalities.KLS.BKL.Localization.contDiff_cumulant_posterior_readable {m : ℕ} (hm : 1 ≤ m) (h : Fin m → EuclideanSpace ℝ (Fin n)) :
    ContDiff ℝ ∞ (fun q : Param n =>
      cumulant (compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n))) m h) := by sorry
