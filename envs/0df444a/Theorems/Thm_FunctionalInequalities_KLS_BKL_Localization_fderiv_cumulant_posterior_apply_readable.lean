-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_fderiv_cumulant_posterior_apply_readable
-- name    : FunctionalInequalities.KLS.BKL.Localization.fderiv_cumulant_posterior_apply_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:14:42.390492+00:00
-- url     : https://prove2.me/theorems/7e33f35a-71f2-43a6-bb75-a119f0e67849
-- title:
--   C-Derivative of a Posterior Cumulant
-- statement:
--   This formalizes the parameter derivative identity for posterior cumulants.
--
--   Let $\mu$ be a compactly supported probability measure on $\mathbb{R}^n$, let $m\ge 1$, let $h:\operatorname{Fin}(m)\to\mathbb{R}^n$, let $p=(c,Q)$ be a localization parameter, and let $v\in\mathbb{R}^n$. Differentiating only in the $c$-direction $(v,0)$ gives
--
--   $$
--   D_c\!\left[\kappa_m(\mu_{c,Q})(h)\right][v]
--   =\kappa_{m+1}(\mu_{c,Q})(h_1,\ldots,h_m,v),
--   $$
--
--   where the right-hand list is represented by `Fin.snoc h v`, and the cumulants are the formalized `cumulant` of the compact posterior.
--
--   The result provides the basic conversion between localization-parameter derivatives and higher posterior cumulants.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.BKL.Localization`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem fderiv_cumulant_posterior_apply {m : ℕ} (hm : 1 ≤ m) (h : Fin m → EuclideanSpace ℝ (Fin n))
--       (p : Param n) (v : EuclideanSpace ℝ (Fin n)) :
--       fderiv ℝ (fun q : Param n =>
--           cumulant (compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n))) m h) p (v, 0) =
--         cumulant (compactPosterior μ hc p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n))) (m + 1) (Fin.snoc h v)
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
--   Previous: [`contDiff_cumulant_posterior`](https://prove2.me/theorems/fae38448-b47c-4a2d-b61a-67ba2745ecc0) · Next: [`inner_cov_apply`](https://prove2.me/theorems/9dacc562-afff-4880-8959-c09a4a246ec3).
--
--   [Source excerpt, lines 128–132](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Localization/CumulantDerivative.lean#L128-L132) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Localization/CumulantDerivative.lean#L126-L192 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Localization.CumulantDerivative`, declaration `FunctionalInequalities.KLS.BKL.Localization.fderiv_cumulant_posterior_apply`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_CumulantDerivative

open MeasureTheory
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Analysis.BakryEmery
variable {n : ℕ} (μ : MeasureTheory.ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).support)

theorem FunctionalInequalities.KLS.BKL.Localization.fderiv_cumulant_posterior_apply_readable {m : ℕ} (hm : 1 ≤ m) (h : Fin m → EuclideanSpace ℝ (Fin n))
    (p : Param n) (v : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fun q : Param n =>
        cumulant (compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n))) m h) p (v, 0) =
      cumulant (compactPosterior μ hc p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n))) (m + 1) (Fin.snoc h v) := by sorry
