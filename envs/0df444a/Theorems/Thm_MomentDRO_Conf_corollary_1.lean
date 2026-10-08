-- Prove2me | Theorems.Thm_MomentDRO_Conf_corollary_1
-- name    : MomentDRO.Conf.corollary_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T08:06:05.102703+00:00
-- url     : https://prove2.me/theorems/c3acf418-39bc-477d-a04c-93fe242c8b36
-- title:
--   Corollary 1, p. 10 — Mahalanobis error of the empirical mean
-- statement:
--   Let $\xi_1,\ldots,\xi_M$ be independent samples from a distribution with mean $\mu$, positive definite covariance $\Sigma$, and finite second moments. Suppose $(\xi-\mu)^\mathsf T\Sigma^{-1}(\xi-\mu)\le R^2$ almost surely for $R\ge0$. For $M\ge1$ and $0<\delta<1$,
--   $$P^M\!\left((\widehat\mu-\mu)^\mathsf T\Sigma^{-1}(\widehat\mu-\mu)\le\beta(\delta)\right)\ge1-\delta,\qquad \beta(\delta)=\frac{R^2}{M}\left(2+\sqrt{2\log(1/\delta)}\right)^2.$$
--
--   This gives the mean constraint of the finite-sample confidence region.
--
--   **Formalization Note** Positive definiteness expresses the section's nonsingular covariance convention. Finite $L^2$ moments make the mean and covariance integrals meaningful. The page says “greater than”; its proof establishes the non-strict lower bound used here.
-- source:
--   Delage & Ye, authors' draft of 20 Feb 2008 (OR 58(3), 2010), p. 10, Corollary 1, (8)

import Mathlib
import Definitions.Def_MomentDRO_Conf_Setting

namespace MomentDRO.Conf

open MeasureTheory

theorem corollary_1 {m M : ℕ} (P : Measure (Fin m → ℝ))
    (hP : HasSecondMoments P) (hcov : (covMat P).PosDef)
    (R : ℝ) (hA4 : Assumption4 P R) (hM : 0 < M)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ENNReal.ofReal (1 - δ) ≤ sampleLaw P M
      {S | quadForm (covMat P)⁻¹ (empMean S - meanVec P) ≤ betaC M R δ} := by sorry

end MomentDRO.Conf
