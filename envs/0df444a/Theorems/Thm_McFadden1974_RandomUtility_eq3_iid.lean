-- Prove2me | Theorems.Thm_McFadden1974_RandomUtility_eq3_iid
-- name    : McFadden1974.RandomUtility.eq3_iid
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T03:43:51.683884+00:00
-- url     : https://prove2.me/theorems/f5bf53b0-7f9e-43d1-a219-28f24d2ccc74
-- title:
--   Equation (3) — the selection probability as an integral, for i.i.d. shocks
-- statement:
--   Let the taste shocks $\varepsilon_1,\dots,\varepsilon_J$ be independent with a common law $\mu$ on $\mathbb{R}$ that has no atoms, and let $G$ be its distribution function. For representative utilities $V_1,\dots,V_J$, the selection probability $P_i$ of Equation (2) (the probability that $V_j + \varepsilon_j < V_i + \varepsilon_i$ for all $j \ne i$) equals
--   $$
--   P_i = \int_{-\infty}^{+\infty} \prod_{j \ne i} G(\varepsilon + V_i - V_j)\, dG(\varepsilon).
--   $$
--
--   This is the i.i.d. form of the paper's Equation (3), $P_i = \int F_i(\varepsilon + V_i - V_1,\dots,\varepsilon + V_i - V_J)\,d\varepsilon$, where $F_i$ is the partial derivative of the joint distribution function in its $i$th argument; it is the integral representation used in Equations (14) and (15) in the proof of Lemma 2, and the starting point of the proof of Lemma 1.
--
--   **Formalization Note** The integral is the Lebesgue–Stieltjes integral against $\mu$, so no density is needed. The no-atom hypothesis makes the strict inequalities of (2) agree with the values $G(t) = \mu((-\infty,t])$; the integrand takes values in $[0,1]$ and is measurable, hence integrable.
-- source:
--   McFadden, Conditional Logit Analysis of Qualitative Choice Behavior, in P. Zarembka (ed.), Frontiers in Econometrics, Academic Press (1974), p. 108, Equation (3) (PDF p. 4); i.i.d. form as in Equations (14)-(15), p. 112 (PDF p. 8)

import Mathlib
import Definitions.Def_McFadden1974_RandomUtility_Model

open MeasureTheory ProbabilityTheory Finset

namespace McFadden1974.RandomUtility

/-- **Equation (3), for i.i.d. shocks** (McFadden, Conditional Logit Analysis of Qualitative
Choice Behavior, in Frontiers in Econometrics (1974), p. 108, Equation (3); PDF p. 4; the i.i.d.
form is the one used in Equations (14)–(15), p. 112, PDF p. 8).
The paper writes (2) as
`P_i = ∫_{ε=−∞}^{+∞} F_i(ε + V_i − V_1, …, ε + V_i − V_J) dε`, with `F_i` the partial derivative
of the joint distribution function `F` in its `i`th argument. For i.i.d. shocks with distribution
function `G`, `F_i(ε + V_i − V_1, …) dε = ∏_{j ≠ i} G(ε + V_i − V_j) dG(ε)`, so (3) reads
`P_i = ∫ ∏_{j ≠ i} G(ε + V_i − V_j) dG(ε)`.

Formalization Note: (3) presupposes that `F` is differentiable; here it is stated with the
Lebesgue–Stieltjes integral `∂μ`, which needs no density, under the hypothesis
`NullSingletonClass μ` (every singleton is `μ`-null, i.e. `μ` has no atoms)
(continuity of `G`). Without it the strict event of (2) would give the left limits
`μ(Iio t)` instead of `G(t) = μ(Iic t)`. The integrand is a product of values of a distribution
function, hence Borel measurable with values in `[0, 1]`, so it is `μ`-integrable. -/
theorem eq3_iid (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ] {J : ℕ}
    (V : Fin J → ℝ) (i : Fin J) :
    selProb μ V i = ∫ ε, ∏ j ∈ univ.erase i, cdf μ (ε + V i - V j) ∂μ := by sorry

end McFadden1974.RandomUtility
