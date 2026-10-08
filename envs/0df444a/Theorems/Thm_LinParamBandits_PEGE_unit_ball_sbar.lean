-- Prove2me | Theorems.Thm_LinParamBandits_PEGE_unit_ball_sbar
-- name    : LinParamBandits.PEGE.unit_ball_sbar
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T02:21:34.396215+00:00
-- url     : https://prove2.me/theorems/c6c85880-829c-47d4-b9c9-d14b3168c2c3
-- title:
--   Sec. 3, p. 15 — the unit ball satisfies SBAR(1)
-- statement:
--   For every $r$, the closed unit ball $\{u \in \mathbb R^r : \|u\| \le 1\}$ satisfies the SBAR(1) condition: every $z \ne 0$ has a unique best arm $u^*(z)$, the maximizer of $u'z$ over the ball, and
--   $$\|u^*(z) - u^*(y)\| \le \|z - y\| \qquad\text{for all unit vectors } z, y.$$
--
--   This is the example the paper gives for the SBAR condition, which makes Theorem 3.1 applicable to the unit ball.
--
--   **Formalization Note** The statement is made for every $r$; the paper's setting is $r \ge 2$.
-- source:
--   Rusmevichientong, Tsitsiklis, Linearly Parameterized Bandits, arXiv:0812.3465v2, Sec. 3, p. 15 ('For some examples, the unit ball satisfies the SBAR(1) condition.')

import Mathlib
import Definitions.Def_LinParamBandits_PEGE_Model

open MeasureTheory ProbabilityTheory

namespace LinParamBandits.PEGE

/-- Sec. 3, p. 15 (Rusmevichientong, Tsitsiklis, arXiv:0812.3465v2): "For some examples, the unit
ball satisfies the SBAR(1) condition." The closed unit ball of `ℝ^r` satisfies SBAR(1). -/
theorem unit_ball_sbar (r : ℕ) : SBAR (Metric.closedBall (0 : LinParamBandits.LowerBound.Vec r) 1) 1 := by sorry
end LinParamBandits.PEGE
