-- Prove2me | Theorems.Thm_HubbleLaw_hubbleParameter_deriv_eq
-- name    : HubbleLaw.hubbleParameter_deriv_eq
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T10:19:26.679326+00:00
-- url     : https://prove2.me/theorems/26577128-4ad6-48e6-89c3-d88930d37ce9
-- title:
--   Time dependence of the Hubble parameter: $\dot H = -(1+q)H^2$
-- statement:
--   **Time dependence of the Hubble parameter.** The Hubble "constant" is constant in space at a
--   fixed time, but varies with time in nearly all cosmological models. On defining the
--   dimensionless deceleration parameter $q = -\ddot a\,a/\dot a^{2}$, the source records the
--   evolution law
--   $$\dot H \;=\; -(1+q)\,H^{2}.$$
--   From it one reads off that $H$ is decreasing in time unless $q < -1$, the phantom-energy
--   regime; and that in the $\Lambda$CDM model, where $q \to -1$ from above, $\dot H \to 0$, so
--   $H$ approaches a constant from above.
--
--   The statement formalizes this for a scale factor that is twice continuously differentiable
--   and everywhere positive, at any time $t$ with $\dot a(t) \ne 0$. The last hypothesis is
--   necessary: $q$ is defined by a quotient with $\dot a^{2}$ in the denominator, and at a time
--   where $\dot a$ vanishes the formula carries no information.
-- source:
--   Wikipedia, "Hubble's law" (Hubble–Lemaître law), https://en.wikipedia.org/wiki/Hubble%27s_law — sections "Recessional velocity" (v = H D, D(t) = (R(t)/R(t_0)) D(t_0)), "Time-dependence of Hubble parameter" (q = -ä a / ȧ², Ḣ = -(1+q)H², exponential growth when H tends to a constant), "Idealized Hubble's law" (the geometric theorem on two points receding from the origin), and "Ultimate fate and age of the universe" (q = 0 gives H = 1/t). PDF of the article supplied by the mission owner.

import Mathlib
import Definitions.Def_HubbleLawDefs

namespace HubbleLaw

theorem hubbleParameter_deriv_eq (a : ℝ → ℝ) (t : ℝ) (ha : ContDiff ℝ 2 a)
    (hpos : ∀ s, 0 < a s) (hd : deriv a t ≠ 0) :
    HasDerivAt (hubbleParameter a)
      (-(1 + decelerationParameter a t) * hubbleParameter a t ^ 2) t := by sorry

end HubbleLaw
