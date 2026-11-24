-- Prove2me | Theorems.Thm_JEPAGeneralization_approximation_error_spectral_jepa
-- name    : JEPAGeneralization.approximation_error_spectral_jepa
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T04:42:14.455794+00:00
-- url     : https://prove2.me/theorems/e00f6bf3-8c80-4ef8-9af6-50c62cfd9ae9
-- title:
--   Theorem 4.3 (as proved): approximation error for spectral JEPA risk
-- statement:
--   Let $w$ be an action-conditioned co-occurrence model on a finite observation space $\mathcal X$ with positive marginals, fix an action $a$, and let $\sigma_1(a)\ge\dots\ge\sigma_{|\mathcal X|}(a)$ be the singular values of $\bar M(a)$. Then the optimal spectral JEPA risk over all encoders $f:\mathcal X\to\mathbb R^k$ and predictors $g:\mathbb R^k\times\mathcal A\to\mathbb R^k$ is
--
--   $$\inf_{f,g}\ \mathcal R_{\mathrm{S\text{-}JEPA}}(f,g,a)=\sum_{i=k+1}^{|\mathcal X|}\sigma_i^2(a).$$
--
--   The approximation error is therefore the tail of the squared singular values of $\bar M(a)$, and it decreases as the latent dimension $k$ grows.
--
--   **Formalization Note** The paper writes $\mathcal R_{\mathrm{S\text{-}JEPA}}(f^*,g^*,a)$ for a minimizer $(f^*,g^*)$. This is stated as an infimum over unconstrained $f$ and $g$, which is what the proof's Eckart–Young argument establishes. A minimizer need not exist: the predictor sees $x$ only through $f(x)$, so the best rank-$k$ factor pair can be unrealizable. Under the normalization of Theorem 3.1 the value is in general strictly larger than the tail sum. The sum is empty when $k\ge|\mathcal X|$.
-- source:
--   Cui, Zhang, Wen, Cheng and Wang, A Generalization Theory for JEPA-Based World Models, arXiv:2606.27014v2 (2026), Section 4.2, Theorem 4.3, eq. (19), p. 6; proof in Appendix A.2, eq. (46)-(53), p. 14

import Mathlib
import Definitions.Def_JEPAGeneralization_Basic

open Finset

namespace JEPAGeneralization

theorem approximation_error_spectral_jepa {X A : Type*} [Fintype X] [DecidableEq X] {k : ℕ}
    (pX : X → ℝ) (w : X → X → A → ℝ) (hw : IsCoOccurrence pX w) (a : A) :
    (⨅ (f : X → Fin k → ℝ) (g : (Fin k → ℝ) → A → Fin k → ℝ), sJepaRisk pX w f g a) =
      ∑ i ∈ Finset.Ico k (Fintype.card X), singVal pX w a i ^ 2 := by sorry

end JEPAGeneralization
