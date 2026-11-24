-- Prove2me | Theorems.Thm_JEPAGeneralization_tuple_risk_unbiased
-- name    : JEPAGeneralization.tuple_risk_unbiased
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T04:44:32.515871+00:00
-- url     : https://prove2.me/theorems/009af65f-2afb-4cc8-8167-1828190b24f1
-- title:
--   Lemma A.4: the tuple risk is unbiased for the empirical JEPA risk
-- statement:
--   Let $w$ be an action-conditioned co-occurrence model on a finite observation space $\mathcal X$ with positive marginals. Fix $f$, $g$, $a$, $m\ge1$ and a dataset $x_1,\dots,x_{2m}$. Draw a uniform permutation $\pi$ of $\{1,\dots,2m\}$ and, for $i=1,\dots,m$, set $z_i=x_{\pi(2i-1)}$, then draw $z_i^+\sim\mathrm P(\cdot\mid z_i,a)$ and $z_i'\sim\mathrm P(\cdot\mid x_{\pi(2i)},a)$, all independently given $\pi$. Then the tuple risk is an unbiased estimator of the empirical JEPA risk:
--
--   $$\mathbb E_S\,\frac1m\sum_{i=1}^m\Big[\big(g(f(z_i),a)^\top f(z_i')\big)^2-2\,g(f(z_i),a)^\top f(z_i^+)\Big]=\hat{\mathcal R}_{2m}(f,g,a),$$
--
--   where $\hat{\mathcal R}_{2m}$ is the empirical JEPA risk of Definition A.1 on $x_1,\dots,x_{2m}$.
--
--   **Formalization Note** The expectation over $\pi$ is the average over all $(2m)!$ permutations, and the expectations over $z_i^+,z_i'$ are exact sums against the transition probabilities. As in Lemma A.2, $f(x')$ in the first term of Definition A.1 is read as $f(x^+)$.
-- source:
--   Cui, Zhang, Wen, Cheng and Wang, A Generalization Theory for JEPA-Based World Models, arXiv:2606.27014v2 (2026), Appendix A.1, Definition A.3, eq. (28)-(29), and Lemma A.4, eq. (30), p. 12

import Mathlib
import Definitions.Def_JEPAGeneralization_Basic

open Finset

namespace JEPAGeneralization

theorem tuple_risk_unbiased {X A : Type*} [Fintype X] {k : ℕ}
    (pX : X → ℝ) (w : X → X → A → ℝ) (hw : IsCoOccurrence pX w)
    (f : X → Fin k → ℝ) (g : (Fin k → ℝ) → A → Fin k → ℝ) (a : A) (m : ℕ) (hm : 1 ≤ m)
    (D : Fin (2 * m) → X) :
    expEmpRiskS pX w f g a D = empRiskN pX w f g a D := by sorry

end JEPAGeneralization
