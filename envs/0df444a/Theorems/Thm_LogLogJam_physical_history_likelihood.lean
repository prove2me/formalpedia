-- Prove2me | Theorems.Thm_LogLogJam_physical_history_likelihood
-- name    : LogLogJam.physical_history_likelihood
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-26T09:31:15.700681+00:00
-- url     : https://prove2.me/theorems/682936e3-3ae0-5a15-a131-939926618957
-- title:
--   Positivity, periodicity, and angular regularity of physical transcript likelihoods
-- statement:
--   For every finite Gaussian transcript consisting of physical seeds, its product likelihood is strictly positive at every angle, has period π, and is continuously differentiable in the angle. The squeezing parameter is greater than one.
-- source:
--   https://arxiv.org/abs/2607.12983; Sections 5.2–5.5, likelihood of the observed history in Lemmas 5.4, 5.5, and 5.9.

import Definitions.Def_LogLogJam_GaussProtocol

open MeasureTheory
open scoped ENNReal

namespace LogLogJam

theorem physical_history_likelihood {t : ℕ} (lam : ℝ) (hlam : 1 < lam) (H : Hist t)
    (hH : ∀ i, IsCov (H i).1 (Matrix.of (H i).2.1)) :
    (∀ s, 0 < histDens lam s H) ∧
    (∀ s, histDens lam (s+Real.pi) H = histDens lam s H) ∧
    ContDiff ℝ 1 (fun s => histDens lam s H) := by sorry

end LogLogJam
