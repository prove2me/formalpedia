-- Prove2me | Theorems.Thm_InfoInundation_Screening_part_b_constant_score
-- name    : InfoInundation.Screening.part_b_constant_score
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:11:49.211189+00:00
-- url     : https://prove2.me/theorems/89d74515-2d10-49a5-b9b2-df5f0f03b787
-- title:
--   Proof of Proposition 1, p. 10 — with known equal accuracy 𝔾 = δ_σ every post has the same score
-- statement:
--   Let the accuracy be deterministic and known, $\mathbb G=\delta_\sigma$ with $\sigma>0$, and let the consumer's belief be $\mathcal N(\mu,s^2)$ with $s>0$. Then for every post value $z$,
--   $$s-\mathbb E\big[s'(\Sigma)\,\big|\,Z=z\big]=s-\sqrt{\frac{s^2\sigma^2}{s^2+\sigma^2}},\qquad s^2-\mathbb E\big[s'(\Sigma)^2\,\big|\,Z=z\big]=s^2-\frac{s^2\sigma^2}{s^2+\sigma^2},$$
--   where $s'(\sigma)$ is the posterior standard deviation of the Belief Updating Equations and the expectations are the Bayes posterior (4). Neither score depends on $z$.
--
--   This is the observation from which part (b) of Proposition 1 follows: given the same accuracy of all posts, the expected decrease in posterior uncertainty from consuming each post is the same.
--
--   **Formalization Note.** Both the printed standard-deviation score and the variance score are covered. The right-hand side of the second identity is written as `s ^ 2 - nextSd s σ ^ 2`.
-- source:
--   Allon, Drakopoulos & Manshadi, Information Inundation on Platforms and Implications, SSRN 3385627 (version of 2020-04-05), p. 10, proof of Proposition 1, first sentence (part (b))

import Mathlib
import Definitions.Def_InfoInundation_Screening_Model
open MeasureTheory ProbabilityTheory

namespace InfoInundation.Screening

theorem part_b_constant_score (σ : ℝ) (hσ : 0 < σ) (μ s : ℝ) (hs : 0 < s) (z : ℝ) :
    sdScore (Measure.dirac σ) μ s z = s - nextSd s σ ∧
      varScore (Measure.dirac σ) μ s z = s ^ 2 - nextSd s σ ^ 2 := by sorry

end InfoInundation.Screening
