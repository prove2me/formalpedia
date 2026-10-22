-- Prove2me | Theorems.Thm_GittinsUCB_Patient_lemma_4
-- name    : GittinsUCB.Patient.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:33:21.596491+00:00
-- url     : https://prove2.me/theorems/0075fe4b-1a36-4252-a2cf-71c26898a9cc
-- title:
--   Lemma 4 — Gaussian positive-part bounds
-- statement:
--   Let $X\sim N(0,\sigma^2)$ with $\sigma>0$, and let $\lambda\ge2\sigma$. With $\phi$ the standard normal density,
--
--   $$\frac{\sigma^4}{\lambda^3}\phi\!\left(\frac\lambda\sigma\right)
--   \le\mathbb E[(X-\lambda)^+]
--   \le\sigma\phi\!\left(\frac\lambda\sigma\right).$$
--
--   The two explicit bounds control the positive part of a Gaussian reward in the upper and lower index estimates.
--
--   **Formalization Note** The printed condition $\lambda\ge\mu+2\sigma$ contains an unused $\mu$ even though $X$ has mean zero. It is read as $\lambda\ge2\sigma$.
-- source:
--   Russo, A Note on the Equivalence of Upper Confidence Bounds and Gittins Indices for Patient Agents, arXiv:1904.04732v1, p. 4, Lemma 4 (stated; proof cited to [17])

import Mathlib
import Definitions.Def_GittinsUCB_Patient_Model
open MeasureTheory ProbabilityTheory Filter Asymptotics NNReal

namespace GittinsUCB.Patient

/-- Lemma 4: both explicit Gaussian positive-part bounds. -/
theorem lemma_4 (σ lam : ℝ) (hσ : 0 < σ) (hlam : 2 * σ ≤ lam) :
    σ ^ 4 / lam ^ 3 * stdPdf (lam / σ) ≤
      (∫ x : ℝ, max (x - lam) 0 ∂(gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩)) ∧
    (∫ x : ℝ, max (x - lam) 0 ∂(gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩)) ≤
      σ * stdPdf (lam / σ) := by sorry

end GittinsUCB.Patient
