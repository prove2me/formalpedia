-- Prove2me | Theorems.Thm_LindleyQueue_Stability_unique_solution
-- name    : LindleyQueue.Stability.unique_solution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:38:59.502993+00:00
-- url     : https://prove2.me/theorems/4dc9cfe3-a205-4d2e-b50e-ebf4fb145c20
-- title:
--   Companion, p. 281 — one and only one d.f. satisfies (5) whenever $\int y\, dG(y) < 0$
-- statement:
--   In Lindley's single-server queue (Assumptions 1–2), let $G$ be the law of $u = s - t$ and suppose
--
--   $$
--   \int y \, dG(y) < 0 .
--   $$
--
--   Then there is exactly one probability distribution $\nu$ on $[0, \infty)$ whose distribution function $H(x) = \nu((-\infty, x])$ satisfies Lindley's integral equation
--
--   $$
--   H(x) = \int_{u \le x} H(x - u)\, dG(u) \qquad \text{for all } x \ge 0
--   $$
--
--   (equivalently, (5): $H(x) = \int_{y \ge 0} H(y)\, dG(x - y)$).
--
--   Existence is the stability theorem (the limit of the waiting-time distributions solves the equation); the content added here is uniqueness, so the equilibrium waiting-time distribution is characterized by the integral equation.
--
--   **Formalization Note** The solution is required to be a probability measure with no mass on $(-\infty, 0)$, i.e. a waiting-time distribution (the paper's $F(x) = 0$ for $x < 0$); without this restriction the equation, which only constrains $x \ge 0$, does not determine $\nu$. $\int y\,dG(y) = \mathscr{E}(u)$ is written as the Bochner integral of `u 0`. Form (4) is used in place of (5), the same integral after $y = x - u$.
-- source:
--   Lindley (Proc. Camb. Phil. Soc. 48, 1952), §4, paragraph after (10), p. 281

import Mathlib
import Definitions.Def_LindleyQueue_Stability_Model
open MeasureTheory ProbabilityTheory Filter Topology

namespace LindleyQueue.Stability

/-- Companion, p. 281: whenever `∫ y dG(y) < 0` there is one and only one distribution
on `[0, ∞)` whose distribution function satisfies (4)–(5) for `x ≥ 0`. -/
theorem unique_solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (Q : Input Ω P) (hneg : ∫ ω, Q.u 0 ω ∂P < 0) :
    ∃! ν : Measure ℝ, IsProbabilityMeasure ν ∧ ν (Set.Iio 0) = 0 ∧
      ∀ x : ℝ, 0 ≤ x → ν.real (Set.Iic x) = ∫ v in Set.Iic x, ν.real (Set.Iic (x - v)) ∂Q.G := by sorry

end LindleyQueue.Stability
