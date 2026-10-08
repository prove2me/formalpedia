-- Prove2me | Theorems.Thm_MomentDRO_Conf_corollary_2
-- name    : MomentDRO.Conf.corollary_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T08:06:23.316344+00:00
-- url     : https://prove2.me/theorems/ce822c27-2c55-423d-8631-7c2f246458b9
-- title:
--   Corollary 2, p. 13 — covariance bounds with known mean
-- statement:
--   Let $\xi_1,\ldots,\xi_M$ be independent samples from a distribution with known mean $\mu$, positive definite covariance $\Sigma$, and finite second moments. Suppose Assumption 4 holds with radius $R$. Write $\widehat\Sigma(\mu)=M^{-1}\sum_i(\xi_i-\mu)(\xi_i-\mu)^\mathsf T$. For $0<\delta<1$ and $M>R^4(\sqrt{1-m/R^4}+\sqrt{\log(2/\delta)})^2$,
--   $$P^M\!\left(\frac{\widehat\Sigma(\mu)}{1+\alpha(\delta/2)}\preceq\Sigma\preceq\frac{\widehat\Sigma(\mu)}{1-\alpha(\delta/2)}\right)\ge1-\delta.$$
--
--   This is the covariance concentration statement before the true mean is replaced by the sample mean.
--
--   **Formalization Note** The explicit threshold spells out “$M$ large enough” via Lemma 3. The page's probability wording is rendered by the non-strict bound derived there.
-- source:
--   Delage & Ye, authors' draft of 20 Feb 2008 (OR 58(3), 2010), pp. 12–13, Corollary 2

import Mathlib
import Definitions.Def_MomentDRO_Conf_Setting

namespace MomentDRO.Conf

open MeasureTheory

theorem corollary_2 {m M : ℕ} (P : Measure (Fin m → ℝ))
    (hP : HasSecondMoments P) (hcov : (covMat P).PosDef)
    (R : ℝ) (hA4 : Assumption4 P R) (δ : ℝ)
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hM : R ^ 4 * (Real.sqrt (1 - (m : ℝ) / R ^ 4) +
      Real.sqrt (Real.log (2 / δ))) ^ 2 < (M : ℝ)) :
    ENNReal.ofReal (1 - δ) ≤ sampleLaw P M
      {S | LoewnerLE ((1 + alphaC M m R (δ / 2))⁻¹ •
          empCovAbout S (meanVec P)) (covMat P) ∧
        LoewnerLE (covMat P) ((1 - alphaC M m R (δ / 2))⁻¹ •
          empCovAbout S (meanVec P))} := by sorry

end MomentDRO.Conf
