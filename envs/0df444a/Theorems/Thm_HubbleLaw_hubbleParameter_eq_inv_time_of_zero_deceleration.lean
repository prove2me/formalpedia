-- Prove2me | Theorems.Thm_HubbleLaw_hubbleParameter_eq_inv_time_of_zero_deceleration
-- name    : HubbleLaw.hubbleParameter_eq_inv_time_of_zero_deceleration
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T10:19:52.425238+00:00
-- url     : https://prove2.me/theorems/f7dee487-9898-4b0e-9382-3ef52c6a4bab
-- title:
--   Zero deceleration gives $H = 1/t$
-- statement:
--   **Zero deceleration gives $H = 1/t$.** The source records that in a universe with deceleration
--   parameter equal to zero it follows that
--   $$H \;=\; \frac{1}{t},$$
--   where $t$ is the time since the Big Bang; the reciprocal $1/H$ of the Hubble parameter — the
--   Hubble time, about $14$ billion years — is then exactly the age of the universe.
--
--   The statement formalizes this with the Big Bang placed at $t = 0$, i.e. $a(0) = 0$: for a
--   twice continuously differentiable scale factor that is positive for all $t > 0$, with
--   $\dot a(t) \ne 0$ and $q(t) = 0$ for all $t > 0$, one has $H(t) = 1/t$ for every $t > 0$.
--   Vanishing deceleration forces $\ddot a = 0$, hence a scale factor growing linearly from the
--   Big Bang, which is the situation the source describes; a non-zero time-dependent $q$ would
--   instead require integrating the Friedmann equations back to the Big Bang.
-- source:
--   Wikipedia, "Hubble's law" (Hubble–Lemaître law), https://en.wikipedia.org/wiki/Hubble%27s_law — sections "Recessional velocity" (v = H D, D(t) = (R(t)/R(t_0)) D(t_0)), "Time-dependence of Hubble parameter" (q = -ä a / ȧ², Ḣ = -(1+q)H², exponential growth when H tends to a constant), "Idealized Hubble's law" (the geometric theorem on two points receding from the origin), and "Ultimate fate and age of the universe" (q = 0 gives H = 1/t). PDF of the article supplied by the mission owner.

import Mathlib
import Definitions.Def_HubbleLawDefs

namespace HubbleLaw

theorem hubbleParameter_eq_inv_time_of_zero_deceleration (a : ℝ → ℝ) (ha : ContDiff ℝ 2 a)
    (h0 : a 0 = 0) (hpos : ∀ s, 0 < s → 0 < a s) (hd : ∀ s, 0 < s → deriv a s ≠ 0)
    (hq : ∀ s, 0 < s → decelerationParameter a s = 0) :
    ∀ t, 0 < t → hubbleParameter a t = 1 / t := by sorry

end HubbleLaw
