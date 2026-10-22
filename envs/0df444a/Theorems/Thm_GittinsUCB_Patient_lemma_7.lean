-- Prove2me | Theorems.Thm_GittinsUCB_Patient_lemma_7
-- name    : GittinsUCB.Patient.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:33:36.580926+00:00
-- url     : https://prove2.me/theorems/500f7ebf-4bb3-4fbc-88d6-a75d539c2894
-- title:
--   Lemma 7 — exploration correction is lower order
-- statement:
--   Let $L_\gamma=\lceil\sigma_W^2[\log(1/(1-\gamma))]^2\rceil$ and
--   $h(\gamma)=-\log L_\gamma+L_\gamma\log\gamma+2\log(1-\sigma_{L_\gamma}^2)+\log\sqrt{2\pi}$.
--   Then the correction term obeys
--
--   $$h(\gamma)=o\!\left(\sqrt{\log\frac1{1-\gamma}}\right)\qquad(\gamma\uparrow1).$$
--
--   This controls the auxiliary term in the paper's lower-bound calculation.
--
--   **Formalization Note** The printed lemma uses $\log(1/\gamma)$, whose square root tends to zero while $h(\gamma)$ does not. Appendix A.2 and the surrounding formulas use $\log(1/(1-\gamma))$; the formal statement adopts that necessary correction.
-- source:
--   Russo, A Note on the Equivalence of Upper Confidence Bounds and Gittins Indices for Patient Agents, arXiv:1904.04732v1, p. 6, Lemma 7; p. 9, Appendix A.2

import Mathlib
import Definitions.Def_GittinsUCB_Patient_Model
open MeasureTheory ProbabilityTheory Filter Asymptotics NNReal

namespace GittinsUCB.Patient

/-- Lemma 7, with the corrected logarithmic scale. -/
theorem lemma_7 (σW2 : ℝ≥0) (hW : 0 < σW2) :
    (fun γ : ℝ => hAux (σW2 : ℝ) γ) =o[nhdsWithin (1 : ℝ) (Set.Iio 1)]
      (fun γ : ℝ => Real.sqrt (Real.log (1 / (1 - γ)))) := by sorry

end GittinsUCB.Patient
