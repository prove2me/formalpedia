-- Prove2me | Theorems.Thm_GittinsUCB_Patient_lemma_3
-- name    : GittinsUCB.Patient.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:33:19.25179+00:00
-- url     : https://prove2.me/theorems/c00b7382-1128-4957-aa95-f62ff15f3d46
-- title:
--   Lemma 3 — Gaussian upper-quantile asymptotic
-- statement:
--   For the standard normal distribution function $\Phi$, its upper quantile satisfies
--
--   $$\Phi^{-1}(\gamma)=\sqrt{2\log\frac1{1-\gamma}}+o(1)\qquad(\gamma\uparrow1).$$
--
--   It connects the index estimates with the prior quantile in the main theorem.
--
--   **Formalization Note** The printed lemma says $\gamma\to\infty$; the quantile domain and Appendix A.1 show that the intended limit is $\gamma\uparrow1$.
-- source:
--   Russo, A Note on the Equivalence of Upper Confidence Bounds and Gittins Indices for Patient Agents, arXiv:1904.04732v1, p. 4, Lemma 3; p. 9, Appendix A.1

import Mathlib
import Definitions.Def_GittinsUCB_Patient_Model
open MeasureTheory ProbabilityTheory Filter Asymptotics NNReal

namespace GittinsUCB.Patient

/-- Lemma 3: the upper normal quantile as the discount approaches one. -/
theorem lemma_3 :
    Tendsto (fun γ : ℝ => stdQuantile γ -
      Real.sqrt (2 * Real.log (1 / (1 - γ))))
      (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0) := by sorry

end GittinsUCB.Patient
