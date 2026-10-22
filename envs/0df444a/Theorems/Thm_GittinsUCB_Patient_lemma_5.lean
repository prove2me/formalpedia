-- Prove2me | Theorems.Thm_GittinsUCB_Patient_lemma_5
-- name    : GittinsUCB.Patient.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:33:26.403574+00:00
-- url     : https://prove2.me/theorems/a3849464-6e07-44de-9b26-f21e97b36afa
-- title:
--   Lemma 5 — Gittins index upper asymptotic bound
-- statement:
--   With standard-normal prior and any positive observation-noise variance, the Gittins index satisfies
--
--   $$\lambda_\gamma(0,1;\sigma_W^2)
--   \le\sqrt{2\log\frac1{1-\gamma}}+o(1)\qquad(\gamma\uparrow1).$$
--
--   This is the upper half of the standardized index asymptotic. Its $o(1)$ inequality is expressed through every positive additive tolerance eventually holding as $\gamma$ approaches one from below.
-- source:
--   Russo, A Note on the Equivalence of Upper Confidence Bounds and Gittins Indices for Patient Agents, arXiv:1904.04732v1, p. 4, Lemma 5

import Mathlib
import Definitions.Def_GittinsUCB_Patient_Model
open MeasureTheory ProbabilityTheory Filter Asymptotics NNReal

namespace GittinsUCB.Patient

/-- Lemma 5: the Gittins index upper bound. -/
theorem lemma_5 (σW2 : ℝ≥0) (hW : 0 < σW2) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ γ : ℝ in nhdsWithin (1 : ℝ) (Set.Iio 1),
        gittinsIndex σW2 γ 0 1 ≤
          Real.sqrt (2 * Real.log (1 / (1 - γ))) + ε := by sorry

end GittinsUCB.Patient
