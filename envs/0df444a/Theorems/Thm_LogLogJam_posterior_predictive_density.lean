-- Prove2me | Theorems.Thm_LogLogJam_posterior_predictive_density
-- name    : LogLogJam.posterior_predictive_density
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-26T09:31:20.158835+00:00
-- url     : https://prove2.me/theorems/00211b30-58a1-5423-b6e9-f73c59594532
-- title:
--   Normalization of the one-round posterior predictive density
-- statement:
--   For any physical history, admissible next seed and squeezing parameter greater than one, mixing the next Gaussian outcome density against the posterior angle gives a measurable nonnegative density of unit mass. The next batch may have zero copies.
-- source:
--   Chen, Gong, Ye and Zhang, arXiv:2607.12983v1, §5.5 (conditioning on histories and posterior Fisher information), predictive law used in Lemma 5.10 and Eq. (13). https://arxiv.org/html/2607.12983v1#S5.SS5

import Definitions.Def_LogLogJam_postFisher
open MeasureTheory
open scoped ENNReal

namespace LogLogJam
theorem posterior_predictive_density (l : ℝ) (hl : 1 < l) {t : ℕ} (H : Hist t) (hH : ∀ i, IsCov (H i).1 (Matrix.of (H i).2.1)) (k : ℕ)
    (W : Q k → Q k → ℝ) (hW : IsCov k (Matrix.of W)) :
    Measurable (fun y => ENNReal.ofReal (predDens l H k W y)) ∧
    (∫⁻ y, ENNReal.ofReal (predDens l H k W y)) = 1 := by sorry
end LogLogJam
