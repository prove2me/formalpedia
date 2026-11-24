-- Prove2me | Theorems.Thm_JEPAGeneralization_sample_error_bound_spectral_jepa
-- name    : JEPAGeneralization.sample_error_bound_spectral_jepa
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T04:45:14.454806+00:00
-- url     : https://prove2.me/theorems/ad0f5aa8-7348-4f3b-833e-dbc78809872d
-- title:
--   Theorem 4.4 (as proved): sample error bound for spectral JEPA risk
-- statement:
--   Let $w$ be an action-conditioned co-occurrence model on a finite nonempty observation space $\mathcal X$ with positive marginals, and fix an action $a$ and $k\ge1$. Let $\mathcal F$ be a nonempty class of encoders $f:\mathcal X\to\mathbb R^k$ and $\mathcal G$ a nonempty class of predictors $g:\mathbb R^k\times\mathcal A\to\mathbb R^k$, all with sup-norm below $\kappa$: $|f(x)_\ell|<\kappa$ and $|g(y,a')_\ell|<\kappa$ for all arguments and coordinates. Let $n=2m$ with $m\ge1$. Let $S=((z_i,z_i^+,z_i'))_{i\le m}$ be the sample of Definition A.3, i.e. $m$ i.i.d. tuples with $z\sim\mathrm P_X$, $z^+\sim\mathrm P(\cdot\mid z,a)$ and $z'\sim w(\cdot\mid a)$. Let $\delta\in(0,1)$. Then with probability at least $1-\delta$ over $S$, every minimizer $(\hat f,\hat g)$ of the tuple risk $\hat{\mathcal R}_S(\cdot,\cdot,a)$ over $\mathcal F\times\mathcal G$ satisfies
--
--   $$\mathcal R_{\mathrm{S\text{-}JEPA}}(\hat f,\hat g,a)-\inf_{f\in\mathcal F,\,g\in\mathcal G}\mathcal R_{\mathrm{S\text{-}JEPA}}(f,g,a)\le c_1\big[\mathfrak R_{n/2}(\mathcal G\circ\mathcal F)+\mathfrak R_{n/2}(\mathcal F)\big]+c_2\Big(\sqrt{\tfrac{\log(2/\delta)}{n}}+\delta\Big),$$
--
--   with $c_1=32k^2\kappa^3+32k\kappa$ and $c_2=8k\kappa^2+2k^2\kappa^4$. Here
--
--   $$\mathfrak R_m(\mathcal F)=\max_\ell\max_{z_1,\dots,z_m}\mathbb E_\sigma\sup_{f\in\mathcal F}\frac1m\sum_{i=1}^m\sigma_if_\ell(z_i)$$
--
--   and
--
--   $$\mathfrak R_m(\mathcal G\circ\mathcal F)=\max_\ell\max_{z_1,\dots,z_m}\mathbb E_\sigma\sup_{f\in\mathcal F,g\in\mathcal G}\frac1m\sum_{i=1}^m\sigma_i\,g(f(z_i),a)_\ell.$$
--
--   This is the sample-error half of the paper's approximation–sample error trade-off. Richer encoder and predictor classes, or a larger $k$, raise the right-hand side.
--
--   **Formalization Note** This is the version the proof establishes. (1) The comparison point is the infimum of the risk over $\mathcal F\times\mathcal G$, not the unrestricted minimizer $(f^*,g^*)$ of Section 3.1. The proof needs $\hat{\mathcal R}_S(f^*,g^*)\le\mathcal R(f^*,g^*)+\epsilon_n$, which uses $(f^*,g^*)\in\mathcal F\times\mathcal G$. With the unrestricted minimizer the printed bound fails: take $\mathcal F=\{0\}$, $\mathcal G=\{0\}$ and small $\kappa$. (2) $\mathfrak R(\mathcal G\circ\mathcal F)$ is the coordinatewise complexity of $x\mapsto g(f(x),a)$ used in the proof (the classes $\mathcal H_{a,\ell}$). The display in the theorem defines it instead as the complexity of the loss class. (3) The sample is the i.i.d. tuple law of Definition A.3, which is the law of the permutation construction. Its probability is an exact finite sum. (4) Minimizers are quantified universally; the paper takes their existence for granted.
-- source:
--   Cui, Zhang, Wen, Cheng and Wang, A Generalization Theory for JEPA-Based World Models, arXiv:2606.27014v2 (2026), Section 4.2, Theorem 4.4, eq. (20), p. 6; proof in Appendix A.2, eq. (54)-(60), pp. 15-16

import Mathlib
import Definitions.Def_JEPAGeneralization_Basic

open Finset

namespace JEPAGeneralization

theorem sample_error_bound_spectral_jepa {X A : Type*} [Fintype X] [Nonempty X] {k : ℕ}
    (hk : 1 ≤ k) (pX : X → ℝ) (w : X → X → A → ℝ) (hw : IsCoOccurrence pX w) (a : A)
    (F : Set (X → Fin k → ℝ)) (hF : F.Nonempty)
    (G : Set ((Fin k → ℝ) → A → Fin k → ℝ)) (hG : G.Nonempty) (κ : ℝ)
    (hFκ : ∀ f ∈ F, ∀ x i, |f x i| < κ) (hGκ : ∀ g ∈ G, ∀ y a' i, |g y a' i| < κ)
    (m : ℕ) (hm : 1 ≤ m) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    1 - δ ≤ sampleProb w a m (fun S => ∀ fh ∈ F, ∀ gh ∈ G,
      (∀ f ∈ F, ∀ g ∈ G, empRiskS fh gh a S ≤ empRiskS f g a S) →
        sJepaRisk pX w fh gh a - (⨅ p : F × G, sJepaRisk pX w p.1.1 p.2.1 a) ≤
          (32 * (k : ℝ) ^ 2 * κ ^ 3 + 32 * k * κ) * (radPred m F G a + radEnc m F) +
            (8 * (k : ℝ) * κ ^ 2 + 2 * (k : ℝ) ^ 2 * κ ^ 4) *
              (Real.sqrt (Real.log (2 / δ) / (2 * m : ℝ)) + δ)) := by sorry

end JEPAGeneralization
