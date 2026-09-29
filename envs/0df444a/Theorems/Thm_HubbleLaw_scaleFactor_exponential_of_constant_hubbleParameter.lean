-- Prove2me | Theorems.Thm_HubbleLaw_scaleFactor_exponential_of_constant_hubbleParameter
-- name    : HubbleLaw.scaleFactor_exponential_of_constant_hubbleParameter
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T10:20:18.921399+00:00
-- url     : https://prove2.me/theorems/d139be98-e791-4265-8881-86e4cd08abec
-- title:
--   A constant Hubble parameter gives exponential expansion
-- statement:
--   **A constant Hubble parameter gives exponential expansion.** In the $\Lambda$CDM model the
--   deceleration parameter tends to $-1$ from above as the cosmological constant comes to dominate
--   over matter, so $H$ approaches a constant value from above — about $57\ \mathrm{(km/s)/Mpc}$ —
--   and the scale factor of the universe then grows exponentially in time.
--
--   The statement isolates the limiting case: if the Hubble parameter of a differentiable,
--   everywhere positive scale factor equals the same value $H_0$ at all times, then for any
--   reference time $t_0$,
--   $$a(t) \;=\; a(t_0)\,e^{H_0 (t - t_0)} \qquad \text{for every } t.$$
--   Exponential growth is thus not an extra modelling assumption but the unique solution of
--   $\dot a = H_0 a$ with the given value at $t_0$. For $H_0 = 0$ the conclusion says that $a$ is
--   constant, and for $H_0 < 0$ it describes exponential contraction.
-- source:
--   Wikipedia, "Hubble's law" (Hubble–Lemaître law), https://en.wikipedia.org/wiki/Hubble%27s_law — sections "Recessional velocity" (v = H D, D(t) = (R(t)/R(t_0)) D(t_0)), "Time-dependence of Hubble parameter" (q = -ä a / ȧ², Ḣ = -(1+q)H², exponential growth when H tends to a constant), "Idealized Hubble's law" (the geometric theorem on two points receding from the origin), and "Ultimate fate and age of the universe" (q = 0 gives H = 1/t). PDF of the article supplied by the mission owner.

import Mathlib
import Definitions.Def_HubbleLawDefs

namespace HubbleLaw

theorem scaleFactor_exponential_of_constant_hubbleParameter
    (a : ℝ → ℝ) (H₀ t₀ : ℝ) (ha : Differentiable ℝ a) (hpos : ∀ s, 0 < a s)
    (hH : ∀ s, hubbleParameter a s = H₀) :
    ∀ t, a t = a t₀ * Real.exp (H₀ * (t - t₀)) := by sorry

end HubbleLaw
