-- Prove2me | Theorems.Thm_InfoInundation_Screening_eq_3
-- name    : InfoInundation.Screening.eq_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:11:19.77999+00:00
-- url     : https://prove2.me/theorems/5f262d3b-a715-43ef-9037-68656d5b0d0f
-- title:
--   (3), p. 10 — the expected decrease in posterior variance equals σ_x⁴ · E[(σ_x² + Σ²)⁻¹ | Z]
-- statement:
--   Let $\mathbb G$ satisfy the standing assumption, let the consumer's belief be $\mathcal N(\mu,s^2)$ with $s>0$, and let $s'(\sigma)^2=s^2\sigma^2/(s^2+\sigma^2)$ be the posterior variance after a post of accuracy $\sigma$ (Belief Updating Equations, ex-post known accuracy). Then for every post value $z$,
--   $$s^2-\mathbb E\big[s'(\Sigma)^2\,\big|\,Z=z;\mu,s\big]=s^4\,\mathbb E\big[(s^2+\Sigma^2)^{-1}\,\big|\,Z=z;\mu,s\big],$$
--   where the posterior expectation is the Bayes ratio (4).
--
--   Consequently the posts maximizing the expected decrease in posterior variance are exactly the posts maximizing $\mathbb E[(\sigma_x(t)^2+\Sigma^2)^{-1}\mid Z_i(t)]$, which is the reformulation (3) of the screening decision in the paper.
--
--   **Formalization Note.** The identity holds for the expected decrease in posterior **variance**, which is the paper's prose description of the screening rule. It does not hold for the printed Screening Equation, which subtracts the expected posterior standard deviation; the goal theorem treats both readings.
-- source:
--   Allon, Drakopoulos & Manshadi, Information Inundation on Platforms and Implications, SSRN 3385627 (version of 2020-04-05), p. 10, proof of Proposition 1, eq. (3)

import Mathlib
import Definitions.Def_InfoInundation_Screening_Model
open MeasureTheory ProbabilityTheory

namespace InfoInundation.Screening

theorem eq_3 (G : Measure ℝ) (hG : AccuracyLaw G) (μ s : ℝ) (hs : 0 < s) (z : ℝ) :
    varScore G μ s z = s ^ 4 * postExp G μ s z (fun σ => (s ^ 2 + σ ^ 2)⁻¹) := by sorry

end InfoInundation.Screening
