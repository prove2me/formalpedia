-- Prove2me | Theorems.Thm_Larmor_retarded_time_on_sphere
-- name    : Larmor.retarded_time_on_sphere
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T01:16:32.030302+00:00
-- url     : https://prove2.me/theorems/6dca54d4-d6de-46d5-ae9b-21d085417212
-- title:
--   For a charge at the origin at time $0$, the retarded time of the sphere $\|x\|=R$ at $t=R/c$ is $0$
-- statement:
--   **The emission event of the observation sphere.** Let $c>0$, let $R>0$ and let the observation time $t$ be determined by $c\,t=R$. Let a point charge move along a worldline $w$ with $w(0)=0$: at time $0$ it passes through the origin. Then for every observation point $x$ at distance $R$ from the origin, the time $0$ is a retarded time for the event $(t,x)$:
--
--   $$0\le t\qquad\text{and}\qquad c\,(t-0)=\|x-w(0)\| .$$
--
--   The content is simply that light emitted from the origin at time $0$ reaches the whole sphere of radius $R$ at time $R/c$. Together with the uniqueness theorem for subluminal worldlines, it identifies the retarded time of every point of the observation sphere as the single emission time $0$ — the instant at which, in the Larmor configuration, the charge is at rest. This is what makes the radiated-power computation an exact identity for each finite radius rather than an asymptotic statement.
-- source:
--   https://en.wikipedia.org/wiki/Larmor_formula — Derivation section (the sphere of radius $R$ about the retarded position of the charge, with $t_r = t - R/c$).

import Definitions.Def_Larmor_lienard_wiechert

namespace Larmor

theorem retarded_time_on_sphere (c R t : ℝ) (hc : 0 < c) (hR : 0 < R) (ht : c * t = R)
    (w : ℝ → Vec) (hw0 : w 0 = 0) (x : Vec) (hx : ‖x‖ = R) :
    IsRetardedTime c w t x 0 := by sorry

end Larmor
