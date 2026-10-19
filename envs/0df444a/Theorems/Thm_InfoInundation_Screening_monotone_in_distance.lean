-- Prove2me | Theorems.Thm_InfoInundation_Screening_monotone_in_distance
-- name    : InfoInundation.Screening.monotone_in_distance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:11:37.057721+00:00
-- url     : https://prove2.me/theorems/a97eab87-2ff5-456c-9efe-88fb07336df7
-- title:
--   p. 10 — E[(σ_x² + Σ²)⁻¹ | Z] is non-increasing in (Z − µ)², strictly decreasing when Supp(𝔾) has two points
-- statement:
--   Let $\mathbb G$ satisfy the standing assumption and let the consumer's belief be $\mathcal N(\mu,s^2)$ with $s>0$. Write $m(z)=\mathbb E\big[(s^2+\Sigma^2)^{-1}\,\big|\,Z=z;\mu,s\big]$ for the Bayes posterior expectation (4) with likelihood (5). Then:
--
--   1. $m$ is a non-increasing function of $(z-\mu)^2$: for all $z,z'$, if $(z-\mu)^2\le(z'-\mu)^2$ then $m(z')\le m(z)$;
--   2. if $\mathbb G$ is not a point mass, $m$ is a strictly decreasing function of $(z-\mu)^2$: if $(z-\mu)^2<(z'-\mu)^2$ then $m(z')<m(z)$.
--
--   Together with (3), this is what makes the closest post the most informative one in expectation.
--
--   **Formalization Note.** The paper states only "non-increasing", which yields that the closest posts are among the maximizers but not the equality of argmax and argmin claimed in Proposition 1 (a). Part 2, under the hypothesis of Proposition 1 (a), is the strict form that equality needs.
-- source:
--   Allon, Drakopoulos & Manshadi, Information Inundation on Platforms and Implications, SSRN 3385627 (version of 2020-04-05), p. 10, proof of Proposition 1, the sentence after eq. (3)

import Mathlib
import Definitions.Def_InfoInundation_Screening_Model
open MeasureTheory ProbabilityTheory

namespace InfoInundation.Screening

theorem monotone_in_distance (G : Measure ℝ) (hG : AccuracyLaw G) (μ s : ℝ) (hs : 0 < s) :
    (∀ z z' : ℝ, (z - μ) ^ 2 ≤ (z' - μ) ^ 2 →
        postExp G μ s z' (fun σ => (s ^ 2 + σ ^ 2)⁻¹) ≤ postExp G μ s z (fun σ => (s ^ 2 + σ ^ 2)⁻¹)) ∧
      ((∀ σ : ℝ, G ≠ Measure.dirac σ) → ∀ z z' : ℝ, (z - μ) ^ 2 < (z' - μ) ^ 2 →
        postExp G μ s z' (fun σ => (s ^ 2 + σ ^ 2)⁻¹) <
          postExp G μ s z (fun σ => (s ^ 2 + σ ^ 2)⁻¹)) := by sorry

end InfoInundation.Screening
