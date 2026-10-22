-- Prove2me | Theorems.Thm_GittinsUCB_Patient_lemma_6
-- name    : GittinsUCB.Patient.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:33:22.592978+00:00
-- url     : https://prove2.me/theorems/3287c397-9064-4b50-8197-1b221cecd1d4
-- title:
--   Lemma 6 — Gittins index lower asymptotic bound
-- statement:
--   With standard-normal prior and any positive observation-noise variance, the Gittins index satisfies
--
--   $$\lambda_\gamma(0,1;\sigma_W^2)
--   \ge\sqrt{2\log\frac1{1-\gamma}}+o(1)\qquad(\gamma\uparrow1).$$
--
--   This matches the upper bound of Lemma 5. The one-sided $o(1)$ inequality means every positive additive tolerance is eventually respected as $\gamma$ approaches one from below.
-- source:
--   Russo, A Note on the Equivalence of Upper Confidence Bounds and Gittins Indices for Patient Agents, arXiv:1904.04732v1, p. 5, Lemma 6; pp. 6–7, proof

import Mathlib
import Definitions.Def_GittinsUCB_Patient_Model
open MeasureTheory ProbabilityTheory Filter Asymptotics NNReal

namespace GittinsUCB.Patient

/-- Lemma 6: the Gittins index lower bound. -/
theorem lemma_6 (σW2 : ℝ≥0) (hW : 0 < σW2) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ γ : ℝ in nhdsWithin (1 : ℝ) (Set.Iio 1),
        Real.sqrt (2 * Real.log (1 / (1 - γ))) - ε ≤
          gittinsIndex σW2 γ 0 1 := by sorry

end GittinsUCB.Patient
