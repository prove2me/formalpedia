-- Prove2me | Theorems.Thm_HubbleLaw_idealized_hubble_law
-- name    : HubbleLaw.idealized_hubble_law
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T10:19:00.905244+00:00
-- url     : https://prove2.me/theorems/f112bbf5-3ef9-489f-b88b-43182996dd5b
-- title:
--   Idealized Hubble's law
-- statement:
--   **Idealized Hubble's law.** The source states the geometric content of Hubble's law as
--   follows: *any two points which are moving away from the origin, each along straight lines and
--   with speed proportional to distance from the origin, will be moving away from each other with
--   a speed proportional to their distance apart.*
--
--   Formally, work in three-dimensional Euclidean space, fix a time $t$ and a proportionality
--   constant $H \ge 0$, and let $p, q : \mathbb{R} \to \mathbb{R}^3$ be the trajectories of two
--   points. The hypothesis "moving away from the origin along a straight line with speed
--   proportional to the distance from the origin, with constant $H$" is the statement that the
--   velocity of each point at time $t$ is $H$ times its position vector:
--   $$p'(t) = H\,p(t), \qquad q'(t) = H\,q(t).$$
--   Then the separation vector $s \mapsto p(s) - q(s)$ is differentiable at $t$ with
--   $$\frac{d}{ds}\Big|_{s=t}\big(p(s)-q(s)\big) \;=\; H\big(p(t)-q(t)\big),$$
--   so the relative velocity is parallel to the separation, and its magnitude is
--   $$\big\lVert H\big(p(t)-q(t)\big)\big\rVert \;=\; H\,\big\lVert p(t)-q(t)\big\rVert,$$
--   that is, $H$ times the distance between the two points. Because $H$ is the same constant for
--   every pair of points, every observer in such an expansion sees the same law, and no point is
--   a distinguished centre of the expansion.
-- source:
--   Wikipedia, "Hubble's law" (Hubble–Lemaître law), https://en.wikipedia.org/wiki/Hubble%27s_law — sections "Recessional velocity" (v = H D, D(t) = (R(t)/R(t_0)) D(t_0)), "Time-dependence of Hubble parameter" (q = -ä a / ȧ², Ḣ = -(1+q)H², exponential growth when H tends to a constant), "Idealized Hubble's law" (the geometric theorem on two points receding from the origin), and "Ultimate fate and age of the universe" (q = 0 gives H = 1/t). PDF of the article supplied by the mission owner.

import Mathlib
import Definitions.Def_HubbleLawDefs

namespace HubbleLaw

theorem idealized_hubble_law (H t : ℝ) (hH : 0 ≤ H)
    (p q : ℝ → EuclideanSpace ℝ (Fin 3))
    (hp : HasDerivAt p (H • p t) t) (hq : HasDerivAt q (H • q t) t) :
    HasDerivAt (fun s => p s - q s) (H • (p t - q t)) t ∧
      ‖H • (p t - q t)‖ = H * ‖p t - q t‖ := by sorry

end HubbleLaw
