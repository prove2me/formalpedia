-- Prove2me | Theorems.Thm_KleywegtSAA_ExpRate_rateFn_pos
-- name    : KleywegtSAA.ExpRate.rateFn_pos
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T00:04:06.997749+00:00
-- url     : https://prove2.me/theorems/c9c3be2f-29ae-4bf0-bd43-28b64d14f7ba
-- title:
--   §2.2, p. 4 — if M(t) < ∞ near t = 0 and a > µ = E X, then I(a) > 0
-- statement:
--   Let $X$ be an integrable real random variable on a probability space with mean $\mu = \mathbb E X$, and suppose its moment generating function $M(t) = \mathbb E\, e^{tX}$ is finite for all $t$ in a neighbourhood of $t = 0$. Then for every $a > \mu$,
--   $$I(a) = \sup_{t \ge 0}\{ta - \log M(t)\} > 0.$$
--
--   Combined with (2.4), this gives an exponentially small probability $P(Z_N \ge a)$ for every level $a$ above the mean.
--
--   **Formalization Note** "Finite in a neighbourhood of $0$" is that $0$ is an interior point of the set of $t$ for which $e^{tX}$ is integrable. Integrability of $X$ follows from it and is kept as a separate hypothesis for readability. $I(a)$ is an extended real and may be $+\infty$.
-- source:
--   Kleywegt & Shapiro, The sample average approximation method for stochastic discrete optimization, preprint (two-author version, sha256 56657748…), p. 4, first paragraph ("Moreover, suppose ... It follows that in that case I(a) > 0")

import Mathlib
import Definitions.Def_KleywegtSAA_ExpRate_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace KleywegtSAA.ExpRate

/-- §2.2, p. 4: if the moment generating function of `Y` is finite in a neighbourhood of `0` and
`a > μ = E Y`, then `I(a) > 0`. -/
theorem rateFn_pos {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℝ) (hY : Integrable Y P) (hA : (0 : ℝ) ∈ interior (integrableExpSet Y P))
    (a : ℝ) (ha : ∫ ω, Y ω ∂P < a) :
    0 < rateFn P Y a := by sorry

end KleywegtSAA.ExpRate
