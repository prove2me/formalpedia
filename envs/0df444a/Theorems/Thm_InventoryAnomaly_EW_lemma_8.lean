-- Prove2me | Theorems.Thm_InventoryAnomaly_EW_lemma_8
-- name    : InventoryAnomaly.EW.lemma_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:27:10.674008+00:00
-- url     : https://prove2.me/theorems/e905bfc9-c944-4efe-a58d-714c8bfc8537
-- title:
--   Lemma 8, p. 34 — a Poisson(λ) variable has sub-exponential norm at most 4λ + 1
-- statement:
--   Let $Y\sim\mathrm{Poisson}(\lambda)$ with $\lambda\ge0$. Its sub-exponential (Orlicz $\psi_1$) norm $\|Y\|_{\psi_1}=\inf\{t>0:\mathbb E\exp(|Y|/t)\le 2\}$ satisfies
--   $$\|Y\|_{\psi_1}\le 4\lambda+1 .$$
--
--   This shows that Poisson noise is sub-exponential with a norm linear in its mean; it is the input to the entrywise matrix-completion bound (Theorem 2) through the paper's Lemma 10.
--
--   **Formalization Note.** The norm is the published `HighDimProb.Concentration.subexponentialNorm`, whose admissible set also requires $\exp(|Y|/t)$ to be integrable; this only excludes Lean's junk value for a non-integrable function. The law is Mathlib's `poissonPMF` as a measure on $\mathbb N$.
-- source:
--   Farias, Li & Peng, Fixing Inventory Inaccuracies at Scale, arXiv:2006.13126v3, p. 34, Lemma 8

import Mathlib
import Definitions.Def_HighDimProb_Concentration_SubexponentialNorm

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InventoryAnomaly.EW

theorem lemma_8 (lam : ℝ≥0) :
    HighDimProb.Concentration.subexponentialNorm (poissonPMF lam).toMeasure (fun k : ℕ => (k : ℝ)) ≤
      4 * (lam : ℝ) + 1 := by sorry

end InventoryAnomaly.EW
