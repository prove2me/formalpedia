-- Prove2me | Theorems.Thm_MinEarnings_Static_static_of_util_increase
-- name    : MinEarnings.Static.static_of_util_increase
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:40:37.403912+00:00
-- url     : https://prove2.me/theorems/9909afad-9e7a-4d02-8554-f24cee8e3049
-- title:
--   Proof of Theorem 3, Online Appendix p. 6 — if utilization rises, u_{t+1} ≥ u_t, under a p = w policy, the marketplace is statically stable
-- statement:
--   Let $D$ and $S$ satisfy the regularity assumptions and let $M>0$. Consider a policy with prices equal to wages, $p_t=w_t\ge 0$, earnings $z_t$ satisfying the equilibrium condition $z_t=w_t\,u_t>0$ with $u_t=u(w_t,z_t)$, and the minimum earnings rule $w_{t+1}\ge M/u_t$ for every $t$. If for some period $t$ the utilization does not drop in the next period,
--   $$u_{t+1}\ \ge\ u_t,$$
--   then the marketplace is statically stable.
--
--   In the proof of Theorem 3 this is the first case of the dynamic-to-static direction, applied to the $p=w$ stable policy given by Lemma 3.
--
--   **Formalization Note** Time is 0-based. Bounded wages and the profit condition are not needed for this step and are not assumed. The equilibrium condition carries $z_t>0$ (see the definition file).
-- source:
--   Asadpour, Lobel & van Ryzin, Minimum Earnings Regulation and the Stability of Marketplaces, SSRN 3502607 (version of August 24, 2022), Online Appendix p. 6 (PDF 34), proof of Theorem 3, first paragraph

import Mathlib
import Definitions.Def_MinEarnings_Static_Setting

namespace MinEarnings.Static

theorem static_of_util_increase (D S : ℝ → ℝ) (M : ℝ) (hP : MinEarnings.Threshold.Primitives D S) (hM : 0 < M)
    (w z : ℕ → ℝ) (hfeas : MinEarnings.Threshold.IsFeasible w w) (heq : MinEarnings.Threshold.IsEquilibrium D S w w z)
    (hrule : MinEarnings.Threshold.MinEarningsRule D S M w w z) (t : ℕ)
    (hinc : MinEarnings.Threshold.util D S (w t) (z t) ≤ MinEarnings.Threshold.util D S (w (t + 1)) (z (t + 1))) :
    IsStaticallyStable D S M := by sorry

end MinEarnings.Static
