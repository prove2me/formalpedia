-- Prove2me | Theorems.Thm_HubbleLaw_redshift_slope_tendsto_hubbleParameter
-- name    : HubbleLaw.redshift_slope_tendsto_hubbleParameter
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T10:26:16.881055+00:00
-- url     : https://prove2.me/theorems/eb94b3d1-41bd-4b9b-8cb7-22e688328fa0
-- title:
--   Linear redshift–distance relation in the small-redshift limit
-- statement:
--   **The linear redshift–distance relation at small redshift.** If light is emitted by a galaxy
--   at time $t_\mathrm{e}$ and received at time $t_0$, the expansion of the universe redshifts it
--   by
--   $$1 + z \;=\; \frac{a(t_0)}{a(t_\mathrm{e})},$$
--   so $z = a(t_0)/a(t_\mathrm{e}) - 1$. The source relates Hubble's law to the observed redshift
--   by a Taylor expansion: if the distance is not too large, the light-travel time is the distance
--   divided by the speed of light, $t_0 - t_\mathrm{e} = D/c$, and one obtains the observational
--   form $z \approx H_0 D / c$, i.e. $v_\mathrm{rs} = cz \approx H_0 D$.
--
--   The statement formalizes the underlying limit exactly, avoiding any approximate equality: as
--   the emission time $t_\mathrm{e}$ approaches the reception time $t_0$ (equivalently, as the
--   source becomes nearby), the ratio of the redshift to the light-travel time converges to the
--   Hubble parameter,
--   $$\lim_{t_\mathrm{e} \to t_0} \frac{z(t_\mathrm{e})}{t_0 - t_\mathrm{e}} \;=\; H(t_0).$$
--   Multiplying by $c$ and using $D = c\,(t_0 - t_\mathrm{e})$ turns this into $cz \approx H_0 D$
--   for nearby sources.
-- source:
--   Wikipedia, "Hubble's law" (Hubble–Lemaître law), https://en.wikipedia.org/wiki/Hubble%27s_law — sections "Recessional velocity" (v = H D, D(t) = (R(t)/R(t_0)) D(t_0)), "Time-dependence of Hubble parameter" (q = -ä a / ȧ², Ḣ = -(1+q)H², exponential growth when H tends to a constant), "Idealized Hubble's law" (the geometric theorem on two points receding from the origin), and "Ultimate fate and age of the universe" (q = 0 gives H = 1/t). PDF of the article supplied by the mission owner.

import Mathlib
import Definitions.Def_HubbleLawDefs

namespace HubbleLaw

theorem redshift_slope_tendsto_hubbleParameter (a : ℝ → ℝ) (t₀ : ℝ)
    (ha : DifferentiableAt ℝ a t₀) (h0 : 0 < a t₀) :
    Filter.Tendsto (fun te => (a t₀ / a te - 1) / (t₀ - te)) (nhdsWithin t₀ {t₀}ᶜ)
      (nhds (hubbleParameter a t₀)) := by sorry

end HubbleLaw
