-- Prove2me | Theorems.Thm_MomentDRO_Conf_lemma_3
-- name    : MomentDRO.Conf.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T08:06:03.602871+00:00
-- url     : https://prove2.me/theorems/d08f3301-c054-4802-b46b-7989e7db2140
-- title:
--   Lemma 3, p. 11 — two-sided Loewner bound for normalized empirical covariance
-- statement:
--   Let $\zeta_1,\ldots,\zeta_M$ be independent samples from a normalized distribution with mean zero, covariance $I$, and $\|\zeta\|_2\le R$ almost surely. Set $\widehat I=M^{-1}\sum_i\zeta_i\zeta_i^\mathsf T$ and $\alpha(t)=\frac{R^2}{\sqrt M}(\sqrt{1-m/R^4}+\sqrt{\log(1/t)})$. If $0<\delta<1$ and $M>R^4(\sqrt{1-m/R^4}+\sqrt{\log(2/\delta)})^2$, then
--   $$P^M\!\left(\frac{\widehat I}{1+\alpha(\delta/2)}\preceq I\preceq\frac{\widehat I}{1-\alpha(\delta/2)}\right)\ge1-\delta.$$
--
--   The bound is the normalized covariance estimate transferred to general covariance in Corollary 2.
--
--   **Formalization Note** The threshold is the page's explicit reading of sufficiently many samples. Matrix order means positive semidefiniteness of the difference. The proof gives a non-strict probability lower bound.
-- source:
--   Delage & Ye, authors' draft of 20 Feb 2008 (OR 58(3), 2010), p. 11, Lemma 3, (10)

import Mathlib
import Definitions.Def_MomentDRO_Conf_Setting

namespace MomentDRO.Conf

open MeasureTheory

theorem lemma_3 {m M : ℕ} (Pζ : Measure (Fin m → ℝ)) (R : ℝ)
    (hζ : IsNormalized Pζ R) (δ : ℝ)
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hM : R ^ 4 * (Real.sqrt (1 - (m : ℝ) / R ^ 4) +
      Real.sqrt (Real.log (2 / δ))) ^ 2 < (M : ℝ)) :
    ENNReal.ofReal (1 - δ) ≤ sampleLaw Pζ M
      {S | LoewnerLE ((1 + alphaC M m R (δ / 2))⁻¹ • empCovAbout S 0)
        (1 : Matrix (Fin m) (Fin m) ℝ) ∧
        LoewnerLE (1 : Matrix (Fin m) (Fin m) ℝ)
          ((1 - alphaC M m R (δ / 2))⁻¹ • empCovAbout S 0)} := by sorry

end MomentDRO.Conf
