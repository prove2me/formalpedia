-- Prove2me | Theorems.Thm_McFadden1974_RandomUtility_lemma1
-- name    : McFadden1974.RandomUtility.lemma1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T03:44:03.111742+00:00
-- url     : https://prove2.me/theorems/f0592398-3a19-4a69-bc51-807d0b377ec1
-- title:
--   Lemma 1 — i.i.d. extreme value shocks give logit selection probabilities
-- statement:
--   Suppose the taste shocks $\varepsilon_1,\dots,\varepsilon_J$ of the random utility model are independent and identically distributed with the extreme value (Gumbel) distribution
--   $$
--   \Pr(\varepsilon_j \le \varepsilon) = e^{-e^{-\varepsilon}} \qquad (\varepsilon \in \mathbb{R}).
--   $$
--   Then for every number $J \ge 1$ of alternatives, every vector of representative utilities $V \in \mathbb{R}^J$ and every alternative $i$, the probability that $i$ maximizes $V_j + \varepsilon_j$ is the logit probability
--   $$
--   P_i = \frac{e^{V_i}}{\sum_{j=1}^J e^{V_j}}.
--   $$
--
--   This is the classical derivation of the conditional logit model from utility maximization, attributed in the paper to Marschak (1959) and to Holman and Marley.
--
--   **Formalization Note** The selection probability is that of Equation (2), with strict inequalities, under the product law of the shocks.
-- source:
--   McFadden, Conditional Logit Analysis of Qualitative Choice Behavior, in P. Zarembka (ed.), Frontiers in Econometrics, Academic Press (1974), p. 111, Lemma 1 (PDF p. 7)

import Mathlib
import Definitions.Def_McFadden1974_RandomUtility_Model

open MeasureTheory ProbabilityTheory Finset

namespace McFadden1974.RandomUtility

/-- **Lemma 1** (McFadden, Conditional Logit Analysis of Qualitative Choice Behavior, in Frontiers
in Econometrics (1974), p. 111, Lemma 1; PDF p. 7): if the values `ε(s, x_j)` are independently
identically distributed with the extreme value distribution (13), `P(ε(s, x_j) ≤ ε) = e^{−e^{−ε}}`,
then the selection probabilities of the random utility model satisfy Equation (12).

Formalization Note: the shocks have common law `μ` and the selection probabilities are those of
(2) (`selProb`), which (3) rewrites for a law with a density such as (13). The conclusion
`IsLogit μ` is (12) for every number `J ≥ 1` of alternatives and every utility vector. -/
theorem lemma1 (μ : Measure ℝ) [IsProbabilityMeasure μ] (h13 : IsExtremeValue μ) :
    IsLogit μ := by sorry

end McFadden1974.RandomUtility
