-- Prove2me | Theorems.Thm_InfoInundation_Screening_cauchy_schwarz_step
-- name    : InfoInundation.Screening.cauchy_schwarz_step
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:11:35.129305+00:00
-- url     : https://prove2.me/theorems/93748adf-3a64-4fc4-9da9-e036513f1494
-- title:
--   p. 11 — Cauchy–Schwarz: E_g[(Σ² + σ_x²)^(−3/2)]² ≤ E_g[(Σ² + σ_x²)^(−5/2)] E_g[(Σ² + σ_x²)^(−1/2)], strict unless 𝔾 is a point mass
-- statement:
--   Let $\mathbb G$ satisfy the standing assumption, let $s>0$ and $r\in\mathbb R$, and let $\mathbb E_g$ be expectation under the auxiliary law $g(\sigma)\propto d\mathbb G(\sigma)\exp\big(-r/(2(\sigma^2+s^2))\big)$. Then
--   $$\mathbb E_g\big[(\Sigma^2+s^2)^{-3/2}\big]^2\le\mathbb E_g\big[(\Sigma^2+s^2)^{-5/2}\big]\,\mathbb E_g\big[(\Sigma^2+s^2)^{-1/2}\big],$$
--   and if $\mathbb G$ is not a point mass (its support contains at least two distinct values) the inequality is strict.
--
--   This is the Cauchy–Schwarz step that fixes the sign of the derivative of $\mathbb E[(\Sigma^2+s^2)^{-1}\mid Z]$ in $(Z-\mu)^2$.
--
--   **Formalization Note.** The paper states only the weak inequality. The strict form is added because Proposition 1 claims an equality of argmax and argmin sets, which needs a strictly decreasing posterior expectation. Strictness uses that the support of $\mathbb G$ lies in $(0,\infty)$: two distinct support points then give two distinct values of $\Sigma^2+s^2$. The statement is for every real $r$; the paper uses $r=(Z-\mu)^2\ge0$.
-- source:
--   Allon, Drakopoulos & Manshadi, Information Inundation on Platforms and Implications, SSRN 3385627 (version of 2020-04-05), p. 11, proof of Proposition 1, the Cauchy–Schwarz display

import Mathlib
import Definitions.Def_InfoInundation_Screening_Model
open MeasureTheory ProbabilityTheory

namespace InfoInundation.Screening

theorem cauchy_schwarz_step (G : Measure ℝ) (hG : AccuracyLaw G) (s : ℝ) (hs : 0 < s) (r : ℝ) :
    auxExp G s r (3 / 2) ^ 2 ≤ auxExp G s r (5 / 2) * auxExp G s r (1 / 2) ∧
      ((∀ σ : ℝ, G ≠ Measure.dirac σ) →
        auxExp G s r (3 / 2) ^ 2 < auxExp G s r (5 / 2) * auxExp G s r (1 / 2)) := by sorry

end InfoInundation.Screening
