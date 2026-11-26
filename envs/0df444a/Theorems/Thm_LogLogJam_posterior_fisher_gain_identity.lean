-- Prove2me | Theorems.Thm_LogLogJam_posterior_fisher_gain_identity
-- name    : LogLogJam.posterior_fisher_gain_identity
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-26T09:41:04.801729+00:00
-- url     : https://prove2.me/theorems/3f9628f2-250d-53f4-bd70-14b44d3f32ae
-- title:
--   Exact Fisher gain for a single posterior update
-- statement:
--   For a physical transcript of any length, a fixed physical next Gaussian seed, and a squeezing parameter greater than one, the predictive expected posterior Fisher information after observing the readout equals the current posterior Fisher information plus the conditional measurement Fisher information integrated against the current posterior on the angle.
-- source:
--   https://arxiv.org/abs/2607.12983, Lemma 5.10, exact conditional-information identity.

import Mathlib
import Definitions.Def_LogLogJam_postFisher

open MeasureTheory
open scoped ENNReal

namespace LogLogJam
theorem posterior_fisher_gain_identity (lam : ℝ) (hlam : 1 < lam) {t : ℕ} (H : Hist t)
    (hH : ∀ i, IsCov (H i).1 (Matrix.of (H i).2.1)) (k : ℕ) (W : Q k → Q k → ℝ)
    (hW : IsCov k (Matrix.of W)) :
    nextCondExp lam H k W (postFisher lam) =
        postFisher lam H +
          ∫⁻ θ in Set.Ico 0 Real.pi, ENNReal.ofReal (post lam H θ) * measFisher lam k W θ := by sorry
end LogLogJam
