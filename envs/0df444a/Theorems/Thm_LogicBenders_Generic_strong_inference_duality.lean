-- Prove2me | Theorems.Thm_LogicBenders_Generic_strong_inference_duality
-- name    : LogicBenders.Generic.strong_inference_duality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:33:21.815359+00:00
-- url     : https://prove2.me/theorems/343f638f-5866-4b72-afad-38ddec1b36b7
-- title:
--   §3, p. 6 — an optimization problem (1) always has the same optimal value as its inference dual (2)
-- statement:
--   Let $D$ be a domain, $S \subseteq D$ a feasible set and $f : D \to \mathbb R$ a real-valued objective. Consider problem (1), $\min f(x)$ subject to $x \in S$, $x \in D$, and its inference dual (2),
--   $$\max \ \beta \quad \text{s.t.} \quad x \in S \xrightarrow{D} f(x) \ge \beta,$$
--   which asks for the largest bound $\beta$ such that $f(x) \ge \beta$ holds at every $x \in D$ satisfying $x \in S$. With optimal values taken in $[-\infty, +\infty]$ (an infeasible minimization has value $+\infty$, an unbounded one $-\infty$, and vice versa for maximization), the two problems have the same optimal value:
--   $$\inf_{x \in S} f(x) \;=\; \sup\{\beta \in [-\infty,+\infty] : f(x) \ge \beta \text{ for all } x \in S\}.$$
--
--   This is the strong duality property of the inference dual. It holds with no assumption on $S$ or $f$, and it is the step of the proof of Theorem 1 that identifies the value $\beta^*$ of the subproblem dual with the optimal value of the subproblem.
--
--   **Formalization Note.** The dual variable $\beta$ ranges over the extended reals, so the convention of §3 is built in: when $S$ is empty every $\beta$ is feasible and both sides are $+\infty$; when $f$ is unbounded below on $S$ only $\beta = -\infty$ is feasible and both sides are $-\infty$.
-- source:
--   Hooker & Ottosson, Logic-based Benders decomposition, revised manuscript (Nov. 2000), p. 6, §3, sentence after display (2) ("A strong duality property obviously holds for the inference dual")

import Mathlib
import Definitions.Def_LogicBenders_Generic_Setting

namespace LogicBenders.Generic

theorem strong_inference_duality {D : Type*} (S : Set D) (f : D → ℝ) :
    optVal1 S f = infDualVal1 S f := by sorry

end LogicBenders.Generic
