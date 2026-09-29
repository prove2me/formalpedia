-- Prove2me | Theorems.Thm_HubbleLaw_properDistance_scaling
-- name    : HubbleLaw.properDistance_scaling
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T04:50:25.423405+00:00
-- url     : https://prove2.me/theorems/1ef54657-f7f0-459f-856d-d0c96d026605
-- title:
--   Proper distances scale with the scale factor
-- statement:
--   **Proper distances scale with the scale factor.** The source introduces the scale factor by
--   the property that all measured proper distances $D(t)$ between comoving points increase
--   proportionally to it:
--   $$D(t) \;=\; \frac{a(t)}{a(t_0)}\,D(t_0),$$
--   where $t_0$ is any reference time. The statement here is exactly this identity for the proper
--   distance between two comoving points with coordinates $\mathbf{x}$ and $\mathbf{y}$, under the
--   standing assumption that the scale factor is positive at both times.
-- source:
--   Wikipedia, "Hubble's law" (Hubble–Lemaître law), https://en.wikipedia.org/wiki/Hubble%27s_law — sections "Recessional velocity" (v = H D, D(t) = (R(t)/R(t_0)) D(t_0)), "Time-dependence of Hubble parameter" (q = -ä a / ȧ², Ḣ = -(1+q)H², exponential growth when H tends to a constant), "Idealized Hubble's law" (the geometric theorem on two points receding from the origin), and "Ultimate fate and age of the universe" (q = 0 gives H = 1/t). PDF of the article supplied by the mission owner.

import Mathlib
import Definitions.Def_HubbleLawDefs

namespace HubbleLaw

theorem properDistance_scaling (a : ℝ → ℝ) (t t₀ : ℝ) (ht : 0 < a t) (ht₀ : 0 < a t₀)
    (x y : EuclideanSpace ℝ (Fin 3)) :
    properDistance a x y t = a t / a t₀ * properDistance a x y t₀ := by sorry

end HubbleLaw
