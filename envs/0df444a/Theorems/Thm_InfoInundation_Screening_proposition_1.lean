-- Prove2me | Theorems.Thm_InfoInundation_Screening_proposition_1
-- name    : InfoInundation.Screening.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:11:50.727734+00:00
-- url     : https://prove2.me/theorems/7c7d370c-467c-4db6-a107-10f7b73f4ea3
-- title:
--   Proposition 1, p. 10 — unknown random accuracy: the screening argmax is the post closest to the belief; known deterministic accuracy: every post
-- statement:
--   **Proposition 1 (Optimality of Consuming Closest Post).** Let the accuracy law $\mathbb G$ satisfy the standing assumption (a probability law whose support lies in some $[\underline\sigma,\overline\sigma]$ with $0<\underline\sigma\le\overline\sigma$). Consider a consumer with belief $\mathcal N(\mu,s^2)$, $s>0$, facing a menu of $K$ posts $Z_1,\dots,Z_K$. Score each post by the expected decrease in posterior uncertainty under ex-post known accuracy, either as printed in the Screening Equation,
--   $$S_{\mathrm{sd}}(Z_i)=s-\mathbb E\big[s'(\Sigma)\,\big|\,Z_i;\mu,s\big],$$
--   or as the expected decrease in posterior variance, $S_{\mathrm{var}}(Z_i)=s^2-\mathbb E[s'(\Sigma)^2\mid Z_i;\mu,s]$, where $s'(\sigma)^2=s^2\sigma^2/(s^2+\sigma^2)$ and the expectation is over the Bayes posterior (4) of the accuracy given the post, with likelihood (5).
--
--   1. **(a)** If the accuracy of posts is random and unknown, i.e. $\mathbb G$ is not a point mass (its support includes at least two distinct values), then for both scores
--   $$\operatorname*{arg\,max}_{1\le i\le K} S(Z_i)=\operatorname*{arg\,min}_{1\le i\le K}(Z_i-\mu)^2 .$$
--   2. **(b)** If the accuracy of posts is deterministic and known, i.e. $\mathbb G=\delta_\sigma$ with $\sigma>0$, then for both scores the argmax is the whole menu $\{1,\dots,K\}$.
--
--   This is the paper's *screening bias*: a consumer who is uncertain about the accuracy of posts and seeks the most informative one picks the post closest to her current belief, while with known equal accuracy she is indifferent among all posts.
--
--   **Formalization Note.** "For any consumer $x$ and time $t$" is rendered as any belief mean $\mu\in\mathbb R$ and standard deviation $s>0$ (states reachable in the paper's dynamics have $s\in(0,1]$). Argmax and argmin are sets of menu indices, so posts with equal values are distinct posts. The page prints the standard-deviation score and describes the rule as the decrease in posterior variance; the statement asserts the conclusion for both. The posterior is the Bayes ratio (4) for an arbitrary $\mathbb G$; no closed form in $(Z-\mu)^2$ is assumed. The standing support bound (in particular $\underline\sigma>0$) is needed: for $\mathbb G=\tfrac12\delta_{-1}+\tfrac12\delta_{1}$ every post has the same score although $\mathbb G$ is not a point mass. Part (a) is stated for ex-post known accuracy $\hat\sigma=\Sigma$; the page's remark that the conclusion also holds for ex-post unknown accuracy is not part of this statement.
-- source:
--   Allon, Drakopoulos & Manshadi, Information Inundation on Platforms and Implications, SSRN 3385627 (version of 2020-04-05), p. 10, Proposition 1 (a) and (b); model of §3, pp. 7–9

import Mathlib
import Definitions.Def_InfoInundation_Screening_Model
open MeasureTheory ProbabilityTheory

namespace InfoInundation.Screening

theorem proposition_1 (G : Measure ℝ) (hG : AccuracyLaw G) (μ s : ℝ) (hs : 0 < s)
    {K : ℕ} (Z : Fin K → ℝ) :
    ((∀ σ : ℝ, G ≠ Measure.dirac σ) →
        argmaxMenu (sdScore G μ s) Z = closestPosts μ Z ∧
          argmaxMenu (varScore G μ s) Z = closestPosts μ Z) ∧
      (∀ σ : ℝ, 0 < σ → G = Measure.dirac σ →
        argmaxMenu (sdScore G μ s) Z = Finset.univ ∧
          argmaxMenu (varScore G μ s) Z = Finset.univ) := by sorry

end InfoInundation.Screening
