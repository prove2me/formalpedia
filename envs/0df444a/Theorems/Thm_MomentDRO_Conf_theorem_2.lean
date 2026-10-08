-- Prove2me | Theorems.Thm_MomentDRO_Conf_theorem_2
-- name    : MomentDRO.Conf.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T08:06:42.219133+00:00
-- url     : https://prove2.me/theorems/bc1243a6-6eba-4097-9a3c-0a8045280d2f
-- title:
--   Theorem 2, p. 13 — simultaneous confidence region for mean and covariance (corrected (12c))
-- statement:
--   Let $\xi_1,\ldots,\xi_M$ be independent samples from a distribution on $\mathbb R^m$ with mean $\mu$, positive definite covariance $\Sigma$, and finite second moments. Assume its normalized squared distance satisfies $(\xi-\mu)^\mathsf T\Sigma^{-1}(\xi-\mu)\le R^2$ almost surely for $R\ge0$. Let $\widehat\mu=M^{-1}\sum_i\xi_i$ and $\widehat\Sigma=M^{-1}\sum_i(\xi_i-\widehat\mu)(\xi_i-\widehat\mu)^\mathsf T$.
--
--   For $M\ge1$ and $0<\delta<1$, define $a=\alpha(\delta/4)=\frac{R^2}{\sqrt M}(\sqrt{1-m/R^4}+\sqrt{\log(4/\delta)})$ and $b=\beta(\delta/2)=\frac{R^2}{M}(2+\sqrt{2\log(2/\delta)})^2$. If $a+b<1$, then with probability at least $1-\delta$ all three constraints hold:
--   $$(\widehat\mu-\mu)^\mathsf T\Sigma^{-1}(\widehat\mu-\mu)\le b,\qquad \Sigma\preceq\frac{\widehat\Sigma}{1-a-b},\qquad \frac{\widehat\Sigma}{1+a}\preceq\Sigma.$$
--
--   This is the paper's finite-sample confidence region for both true moments, obtained from empirical estimates and the normalized support radius.
--
--   **Formalization Note** The condition $a+b<1$ makes the upper covariance denominator positive and specifies the page's “$M$ large enough.” Equation (12c) prints $1/(1-a)$, but the paper's own union-bound display on p. 13 yields $1/(1+a)$; the printed version is false even for Rademacher observations $\xi=\pm1$, where $\widehat\Sigma=1-\widehat\mu^2$. The statement uses the corrected bound. The page says “greater than $1-\delta$”; its union bounds establish the non-strict form used here.
-- source:
--   Delage & Ye, authors' draft of 20 Feb 2008 (OR 58(3), 2010), pp. 13–14, Theorem 2, (12a)–(12c), corrected (12c) from p. 13 union-bound display

import Mathlib
import Definitions.Def_MomentDRO_Conf_Setting

namespace MomentDRO.Conf

open MeasureTheory

theorem theorem_2 {m M : ℕ} (P : Measure (Fin m → ℝ))
    (hP : HasSecondMoments P) (hcov : (covMat P).PosDef)
    (R : ℝ) (hA4 : Assumption4 P R) (hM : 0 < M)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hlarge : alphaC M m R (δ / 4) + betaC M R (δ / 2) < 1) :
    ENNReal.ofReal (1 - δ) ≤ sampleLaw P M
      {S | quadForm (covMat P)⁻¹ (empMean S - meanVec P) ≤ betaC M R (δ / 2) ∧
        LoewnerLE (covMat P)
          ((1 - alphaC M m R (δ / 4) - betaC M R (δ / 2))⁻¹ • empCov S) ∧
        LoewnerLE ((1 + alphaC M m R (δ / 4))⁻¹ • empCov S)
          (covMat P)} := by sorry

end MomentDRO.Conf
