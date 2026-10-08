-- Prove2me | Theorems.Thm_MomentDRO_Conf_lemma_2
-- name    : MomentDRO.Conf.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T08:05:43.53513+00:00
-- url     : https://prove2.me/theorems/e5f492e7-e35c-4173-a9a9-1ecf0bbf78a7
-- title:
--   Lemma 2, p. 10 — bounded normalized sample mean
-- statement:
--   Let $\zeta_1,\ldots,\zeta_M$ be independent samples of a normalized random vector in $\mathbb R^m$: $\mathbb E\zeta=0$, $\mathbb E[\zeta\zeta^\mathsf T]=I$, and $\|\zeta\|_2\le R$ almost surely. For $M\ge1$ and $0<\delta<1$, the empirical mean $\overline\zeta=M^{-1}\sum_i\zeta_i$ satisfies
--   $$P^M\!\left(\|\overline\zeta\|_2^2\le\frac{R^2}{M}\left(2+\sqrt{2\log(1/\delta)}\right)^2\right)\ge1-\delta.$$
--
--   This is the bounded-sample mean estimate used to obtain Corollary 1 for a general nonsingular covariance.
--
--   **Formalization Note** $P^M$ is the product measure, and squared Euclidean length is a dot product. The normalization includes finite second moments so that its mean and covariance are genuine integrals.
-- source:
--   Delage & Ye, authors' draft of 20 Feb 2008 (OR 58(3), 2010), p. 10, Lemma 2; attributed there to Shawe-Taylor and Cristianini (2003)

import Mathlib
import Definitions.Def_MomentDRO_Conf_Setting

namespace MomentDRO.Conf

open MeasureTheory

theorem lemma_2 {m M : ℕ} (Pζ : Measure (Fin m → ℝ)) (R : ℝ)
    (hζ : IsNormalized Pζ R) (hM : 0 < M) (δ : ℝ)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ENNReal.ofReal (1 - δ) ≤ sampleLaw Pζ M
      {S | empMean S ⬝ᵥ empMean S ≤ betaC M R δ} := by sorry

end MomentDRO.Conf
