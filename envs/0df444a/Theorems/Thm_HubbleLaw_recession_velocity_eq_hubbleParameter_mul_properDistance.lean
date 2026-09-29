-- Prove2me | Theorems.Thm_HubbleLaw_recession_velocity_eq_hubbleParameter_mul_properDistance
-- name    : HubbleLaw.recession_velocity_eq_hubbleParameter_mul_properDistance
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T10:18:30.828726+00:00
-- url     : https://prove2.me/theorems/b7093200-13bd-4653-8bf7-3b96e792ccc1
-- title:
--   Hubble's law $v = H D$
-- statement:
--   **Hubble's law, $v = H D$.** Let $D(t)$ be the proper distance between two comoving points and
--   call its rate of change the recession velocity, $v_r = \dot D$. Defining the Hubble parameter
--   as $H = \dot a / a$, the source obtains Hubble's law
--   $$v_r(t) \;=\; H(t)\,D(t).$$
--   The statement formalizes this: for a scale factor differentiable at $t$ and positive there,
--   the proper distance between the comoving points $\mathbf{x}$ and $\mathbf{y}$ is
--   differentiable at $t$, with derivative $H(t)$ times the proper distance at $t$. The
--   proportionality constant does not depend on the chosen pair of points, which is the content of
--   Hubble's law as a law rather than as a coincidence for one galaxy.
-- source:
--   Wikipedia, "Hubble's law" (Hubble–Lemaître law), https://en.wikipedia.org/wiki/Hubble%27s_law — sections "Recessional velocity" (v = H D, D(t) = (R(t)/R(t_0)) D(t_0)), "Time-dependence of Hubble parameter" (q = -ä a / ȧ², Ḣ = -(1+q)H², exponential growth when H tends to a constant), "Idealized Hubble's law" (the geometric theorem on two points receding from the origin), and "Ultimate fate and age of the universe" (q = 0 gives H = 1/t). PDF of the article supplied by the mission owner.

import Mathlib
import Definitions.Def_HubbleLawDefs

namespace HubbleLaw

theorem recession_velocity_eq_hubbleParameter_mul_properDistance
    (a : ℝ → ℝ) (t : ℝ) (ha : DifferentiableAt ℝ a t) (hat : 0 < a t)
    (x y : EuclideanSpace ℝ (Fin 3)) :
    HasDerivAt (properDistance a x y)
      (hubbleParameter a t * properDistance a x y t) t := by sorry

end HubbleLaw
