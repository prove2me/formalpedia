-- Prove2me | Theorems.Thm_InfoInundation_Screening_aux_density_ratio
-- name    : InfoInundation.Screening.aux_density_ratio
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:11:26.239231+00:00
-- url     : https://prove2.me/theorems/8db23263-739a-4962-a893-5692f93e31f9
-- title:
--   p. 11 — E[(Σ² + σ_x²)⁻¹ | Z] = E_g[(Σ² + σ_x²)^(−3/2)] / E_g[(Σ² + σ_x²)^(−1/2)] under the auxiliary density g
-- statement:
--   Let $\mathbb G$ satisfy the standing assumption, let the consumer's belief be $\mathcal N(\mu,s^2)$ with $s>0$, and write $r=(z-\mu)^2$ for a post value $z$. Let $g$ be the auxiliary probability law on the accuracy with density proportional to
--   $$g(\sigma)\propto d\mathbb G(\sigma)\,\exp\Big(-\frac{r}{2(\sigma^2+s^2)}\Big),$$
--   and write $\mathbb E_g$ for expectation under it. Then
--   $$\mathbb E\big[(\Sigma^2+s^2)^{-1}\,\big|\,Z=z;\mu,s\big]=\frac{\mathbb E_g\big[(\Sigma^2+s^2)^{-3/2}\big]}{\mathbb E_g\big[(\Sigma^2+s^2)^{-1/2}\big]},$$
--   where the left side is the Bayes posterior expectation (4) with likelihood (5).
--
--   The rewrite moves the dependence on the post into the auxiliary density, which depends on $z$ only through $r=(z-\mu)^2$; this is the form in which the paper differentiates in $r$.
--
--   **Formalization Note.** $\mathbb E_g[(\Sigma^2+s^2)^{-p}]$ is `auxExp G s r p`, the ratio of $\int(\sigma^2+s^2)^{-p}e^{-r/(2(\sigma^2+s^2))}d\mathbb G$ to the same integral with $p=0$.
-- source:
--   Allon, Drakopoulos & Manshadi, Information Inundation on Platforms and Implications, SSRN 3385627 (version of 2020-04-05), p. 11, proof of Proposition 1, first display and the definition of g

import Mathlib
import Definitions.Def_InfoInundation_Screening_Model
open MeasureTheory ProbabilityTheory

namespace InfoInundation.Screening

theorem aux_density_ratio (G : Measure ℝ) (hG : AccuracyLaw G) (μ s : ℝ) (hs : 0 < s) (z : ℝ) :
    postExp G μ s z (fun σ => (σ ^ 2 + s ^ 2)⁻¹) =
      auxExp G s ((z - μ) ^ 2) (3 / 2) / auxExp G s ((z - μ) ^ 2) (1 / 2) := by sorry

end InfoInundation.Screening
