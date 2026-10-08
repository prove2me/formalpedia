-- Prove2me | Theorems.Thm_McFadden1974_RandomUtility_logit_iff_extreme_value
-- name    : McFadden1974.RandomUtility.logit_iff_extreme_value
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T03:44:35.949374+00:00
-- url     : https://prove2.me/theorems/ac6e2d7e-7d91-4059-b8c3-72a5b1254ef7
-- title:
--   Lemmas 1 and 2 — logit selection probabilities if and only if extreme value shocks
-- statement:
--   Fix a universe $X$ and a surjective representative utility map $u:X\to\mathbb R$. Let the taste shocks of the random utility model be independent and identically distributed with a translation complete law $\mu$ on $\mathbb{R}$ whose distribution function $G$ satisfies the normalization $G(0) = e^{-1}$. Then the following are equivalent:
--
--   1. for every finite subset $B\subseteq X$ and every alternative $i\in B$,
--   $$
--   \Pr\big[u(j) + \varepsilon_j < u(i) + \varepsilon_i \ \text{for all } j \ne i\big] = \frac{e^{u(i)}}{\sum_{j\in B} e^{u(j)}};
--   $$
--   2. $G(\varepsilon) = e^{-e^{-\varepsilon}}$ for every real $\varepsilon$.
--
--   This is the characterization announced on p. 111 of the paper: "under mild conditions the distribution (13) characterizes the population choice models whose selection probabilities satisfy Equation (12)". It justifies reading a conditional logit model as a model of utility-maximizing individuals with extreme value taste shocks.
--
--   **Formalization Note** Direction 2 ⇒ 1 is Lemma 1 and needs neither translation completeness nor the normalization; 1 ⇒ 2 is Lemma 2. The hypotheses are satisfiable: the extreme value law is translation complete (footnote 5 of the paper) and has $G(0) = e^{-1}$. Condition 1 is required for every finite subset of the stated universe; distinct alternatives may have equal utilities.
-- source:
--   McFadden, Conditional Logit Analysis of Qualitative Choice Behavior, in P. Zarembka (ed.), Frontiers in Econometrics, Academic Press (1974), pp. 111-112, Lemmas 1 and 2 (PDF pp. 7-8)

import Mathlib
import Definitions.Def_McFadden1974_RandomUtility_Model

open MeasureTheory ProbabilityTheory Finset

namespace McFadden1974.RandomUtility

/-- **Lemmas 1 and 2 — the extreme value law characterizes logit random utility models**
(McFadden, Conditional Logit Analysis of Qualitative Choice Behavior, in Frontiers in Econometrics
(1974), pp. 111–112, Lemmas 1 and 2; PDF pp. 7–8; p. 111: "The next lemma establishes that under
mild conditions the distribution (13) characterizes the population choice models whose selection
probabilities satisfy Equation (12).").

Fix an alternative universe `X` and a representative utility map `u : X → ℝ` that is onto.
Let the shocks be i.i.d. with a translation complete law `μ` normalized by `G(0) = e^{−1}`.
Then the selection probabilities on every finite subset of `X` satisfy (12) if and only if
`G(ε) = e^{−e^{−ε}}` for every `ε`.

Formalization Note: the direction ← is Lemma 1 (which needs neither translation completeness nor
the normalization); → is Lemma 2 with the normalization `G(0) = e^{−1}`. The hypotheses are
satisfiable: the law (13) is translation complete (footnote 5, p. 111) and has `G(0) = e^{−1}`.
The selection probabilities are those of (2), with strict inequalities and no density assumed;
`IsLogitOn` covers finite subsets of `X`, including repeated utility values. -/
theorem logit_iff_extreme_value (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {X : Type*} (u : X → ℝ) (hu : Function.Surjective u)
    (hTC : TranslationComplete μ) (h0 : cdf μ 0 = Real.exp (-1)) :
    IsLogitOn μ u ↔ IsExtremeValue μ := by sorry

end McFadden1974.RandomUtility
