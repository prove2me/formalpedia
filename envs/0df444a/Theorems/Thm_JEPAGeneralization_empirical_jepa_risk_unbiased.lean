-- Prove2me | Theorems.Thm_JEPAGeneralization_empirical_jepa_risk_unbiased
-- name    : JEPAGeneralization.empirical_jepa_risk_unbiased
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T04:43:38.867876+00:00
-- url     : https://prove2.me/theorems/d8d19925-f8cd-4604-89fe-1ec0df4b8e0c
-- title:
--   Lemma A.2: the empirical JEPA risk is unbiased
-- statement:
--   Let $w$ be an action-conditioned co-occurrence model on a finite observation space $\mathcal X$ with positive marginals. Fix an encoder $f$, a predictor $g$, an action $a$ and $n\ge2$. Let $x_1,\dots,x_n$ be i.i.d. from $\mathrm P_X$, and let
--
--   $$\hat{\mathcal R}_n(f,g,a)=-2\,\frac1n\sum_{i=1}^n\mathbb E_{x^+\sim\mathrm P(\cdot\mid x_i,a)}\big[g(f(x_i),a)^\top f(x^+)\big]+\frac1{n(n-1)}\sum_{i\ne j}\mathbb E_{x'\sim\mathrm P(\cdot\mid x_j,a)}\big[g(f(x_i),a)^\top f(x')\big]^2.$$
--
--   Then $\hat{\mathcal R}_n$ is an unbiased estimator of the population spectral loss:
--
--   $$\mathbb E_{x_1,\dots,x_n}\hat{\mathcal R}_n(f,g,a)=\mathbb E\Big[\big(g(f(z),a)^\top f(z')\big)^2-2\,g(f(z),a)^\top f(z^+)\Big],$$
--
--   with $z\sim\mathrm P_X$, $z^+\sim\mathrm P(\cdot\mid z,a)$ and an independent $z'\sim w(\cdot\mid a)$.
--
--   **Formalization Note** In Definition A.1 the first term reads $g(f(x),a)^\top f(x')$ with $x'$ unbound, and it is read as $f(x^+)$. The lemma's $\mathcal R(f,g,a)$ is not defined in the paper. It is taken to be the spectral loss, the form of the risk used in the proof of Theorem 4.4. This equals $\mathcal R_{\mathrm{S\text{-}JEPA}}-\|\bar M(a)\|_F^2$, and for normalized $(f,g)$ it equals $\mathcal R_{\mathrm{JEPA}}-2$. The pairs $(x_i,x_j)$, $i\ne j$, are ordered.
-- source:
--   Cui, Zhang, Wen, Cheng and Wang, A Generalization Theory for JEPA-Based World Models, arXiv:2606.27014v2 (2026), Appendix A.1, Definition A.1, eq. (26), and Lemma A.2, eq. (27), p. 12

import Mathlib
import Definitions.Def_JEPAGeneralization_Basic

open Finset

namespace JEPAGeneralization

theorem empirical_jepa_risk_unbiased {X A : Type*} [Fintype X] {k : ℕ}
    (pX : X → ℝ) (w : X → X → A → ℝ) (hw : IsCoOccurrence pX w)
    (f : X → Fin k → ℝ) (g : (Fin k → ℝ) → A → Fin k → ℝ) (a : A) (n : ℕ) (hn : 2 ≤ n) :
    ∑ D : Fin n → X, datasetProb pX D * empRiskN pX w f g a D = spectralLoss pX w f g a := by sorry

end JEPAGeneralization
