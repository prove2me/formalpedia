-- Prove2me | Theorems.Thm_NewtonGravitation_hasGradientAt_pointPotential
-- name    : NewtonGravitation.hasGradientAt_pointPotential
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-27T17:43:21.417142+00:00
-- url     : https://prove2.me/theorems/295b8e66-67cf-491f-a0ec-878d8e89f0fc
-- title:
--   The point-mass field is conservative: $g = -\nabla V$
-- statement:
--   Let $M\in\mathbb{R}$ and $c\in\mathbb{E}^3$, and let $V(x) = -\frac{GM}{\|x-c\|}$ be the gravitational potential of a point mass $M$ at $c$. At every point $x\neq c$, $V$ is differentiable and
--   $$\nabla V(x) = -g(x),\qquad g(x) = -\frac{GM}{\|x-c\|^3}(x-c).$$
--
--   This is the statement of the source's *Gravity field* section that gravitational fields are conservative, with potential $V$ satisfying $g = -\nabla V$, specialised to a point mass.
-- source:
--   Wikipedia, "Newton's law of universal gravitation", revision oldid=1370960529 (https://en.wikipedia.org/w/index.php?title=Newton%27s_law_of_universal_gravitation&oldid=1370960529)

import Definitions.Def_NewtonGravitation_Defs
import Mathlib

open MeasureTheory NewtonGravitation

namespace NewtonGravitation

theorem hasGradientAt_pointPotential (M : ℝ) (c x : Space) (hx : x ≠ c) :
    HasGradientAt (pointPotential M c) (-pointField M c x) x := by sorry

end NewtonGravitation
