-- Prove2me | Theorems.Thm_HubbleLaw_comoving_velocity_eq_hubbleParameter_smul_position
-- name    : HubbleLaw.comoving_velocity_eq_hubbleParameter_smul_position
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T10:16:45.706676+00:00
-- url     : https://prove2.me/theorems/48fee60a-04fd-4df3-8e0b-3e4eac4322ab
-- title:
--   Velocity of a comoving point is $H(t)$ times its position vector
-- statement:
--   **The velocity of a comoving point is $H(t)$ times its position vector.** In the source's
--   derivation, a comoving point at comoving coordinate $\mathbf{x}$ has proper position
--   $\mathbf{X}(t) = a(t)\mathbf{x}$, and differentiating gives
--   $$\dot{\mathbf{X}}(t) \;=\; \dot a(t)\,\mathbf{x} \;=\; \frac{\dot a(t)}{a(t)}\,\mathbf{X}(t)
--   \;=\; H(t)\,\mathbf{X}(t).$$
--   This is the vector form of Hubble's law, and it is exactly the hypothesis of the idealized
--   Hubble law: every comoving point moves radially away from the origin with speed proportional
--   to its distance from it, with the same proportionality constant $H(t)$ for all points. The
--   statement assumes that $a$ is differentiable at $t$ and that $a(t) \ne 0$, the latter being
--   needed for $H(t)$ to be the correct proportionality constant.
-- source:
--   Wikipedia, "Hubble's law" (Hubble–Lemaître law), https://en.wikipedia.org/wiki/Hubble%27s_law — sections "Recessional velocity" (v = H D, D(t) = (R(t)/R(t_0)) D(t_0)), "Time-dependence of Hubble parameter" (q = -ä a / ȧ², Ḣ = -(1+q)H², exponential growth when H tends to a constant), "Idealized Hubble's law" (the geometric theorem on two points receding from the origin), and "Ultimate fate and age of the universe" (q = 0 gives H = 1/t). PDF of the article supplied by the mission owner.

import Mathlib
import Definitions.Def_HubbleLawDefs

namespace HubbleLaw

theorem comoving_velocity_eq_hubbleParameter_smul_position
    (a : ℝ → ℝ) (t : ℝ) (ha : DifferentiableAt ℝ a t) (hat : a t ≠ 0)
    (x : EuclideanSpace ℝ (Fin 3)) :
    HasDerivAt (properPosition a x) (hubbleParameter a t • properPosition a x t) t := by sorry

end HubbleLaw
