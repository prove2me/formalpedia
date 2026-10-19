-- Prove2me | Theorems.Thm_InfoInundation_Screening_derivative_display
-- name    : InfoInundation.Screening.derivative_display
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:11:35.153978+00:00
-- url     : https://prove2.me/theorems/807cfc24-f732-464e-873d-4aba7d4448de
-- title:
--   p. 11 — the derivative of E_g[w^(3/2)]/E_g[w^(1/2)] in (Z − µ)² is ½(−E_g[w^(5/2)]E_g[w^(1/2)] + E_g[w^(3/2)]²)/E_g[w^(1/2)]² ≤ 0
-- statement:
--   Let $\mathbb G$ satisfy the standing assumption and $s>0$. For $r\in\mathbb R$ let $\mathbb E_{g_r}$ be expectation under the auxiliary law $g_r(\sigma)\propto d\mathbb G(\sigma)\exp\big(-r/(2(\sigma^2+s^2))\big)$, and set
--   $$\Phi(r)=\frac{\mathbb E_{g_r}\big[(\Sigma^2+s^2)^{-3/2}\big]}{\mathbb E_{g_r}\big[(\Sigma^2+s^2)^{-1/2}\big]},$$
--   which by the auxiliary-density rewrite equals $\mathbb E[(\Sigma^2+s^2)^{-1}\mid Z]$ when $r=(Z-\mu)^2$. Then $\Phi$ is differentiable at every $r$, with
--   $$\Phi'(r)=\frac12\cdot\frac{-\mathbb E_{g_r}\big[(\Sigma^2+s^2)^{-5/2}\big]\,\mathbb E_{g_r}\big[(\Sigma^2+s^2)^{-1/2}\big]+\mathbb E_{g_r}\big[(\Sigma^2+s^2)^{-3/2}\big]^2}{\mathbb E_{g_r}\big[(\Sigma^2+s^2)^{-1/2}\big]^2}\le0 .$$
--
--   This is the derivative computation of the proof of Proposition 1: the posterior expectation of $(\Sigma^2+s^2)^{-1}$ is non-increasing in the squared distance between the post and the belief.
--
--   **Formalization Note.** The page prints the derivative without the factor $\tfrac12$. Since $\partial g/\partial r=-g/(2(\sigma^2+s^2))$, as the page itself states, the correct derivative carries the factor $\tfrac12$; the sign, which is all the proof uses, is unchanged. The statement is for every real $r$; the paper uses $r\ge0$.
-- source:
--   Allon, Drakopoulos & Manshadi, Information Inundation on Platforms and Implications, SSRN 3385627 (version of 2020-04-05), p. 11, proof of Proposition 1, the derivative display (corrected by the factor 1/2)

import Mathlib
import Definitions.Def_InfoInundation_Screening_Model
open MeasureTheory ProbabilityTheory

namespace InfoInundation.Screening

theorem derivative_display (G : Measure ℝ) (hG : AccuracyLaw G) (s : ℝ) (hs : 0 < s) (r : ℝ) :
    HasDerivAt (fun r' => auxExp G s r' (3 / 2) / auxExp G s r' (1 / 2))
        ((1 / 2) * (-(auxExp G s r (5 / 2) * auxExp G s r (1 / 2)) + auxExp G s r (3 / 2) ^ 2) /
          auxExp G s r (1 / 2) ^ 2) r ∧
      (1 / 2) * (-(auxExp G s r (5 / 2) * auxExp G s r (1 / 2)) + auxExp G s r (3 / 2) ^ 2) /
          auxExp G s r (1 / 2) ^ 2 ≤ 0 := by sorry

end InfoInundation.Screening
