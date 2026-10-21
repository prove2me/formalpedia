-- Prove2me | Theorems.Thm_MinEarnings_Static_static_of_wage_ge
-- name    : MinEarnings.Static.static_of_wage_ge
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:40:32.118895+00:00
-- url     : https://prove2.me/theorems/946118b4-53a5-4fff-88a5-21ebb80e8201
-- title:
--   Proof of Theorem 3, Online Appendix p. 6 — if w_t ≥ M/u_t for some t under a p = w policy, the marketplace is statically stable
-- statement:
--   Let $D$ and $S$ satisfy the regularity assumptions and let $M>0$. Consider a policy with prices equal to wages, $p_t=w_t\ge 0$, earnings $z_t$ satisfying the equilibrium condition $z_t=w_t\,u_t>0$ with $u_t=u(w_t,z_t)$, and the minimum earnings rule $w_{t+1}\ge M/u_t$ for every $t$. If for some period $t$ the wage already meets the same-period floor,
--   $$w_t\ \ge\ \frac{M}{u_t},$$
--   then the marketplace is statically stable.
--
--   In the proof of Theorem 3 this is the second case of the dynamic-to-static direction.
--
--   **Formalization Note** Time is 0-based. The hypothesis compares $w_t$ with the floor computed from the *same* period's utilization, as in (8), not with the rule's next-period floor. Bounded wages and the profit condition are not needed for this step and are not assumed.
-- source:
--   Asadpour, Lobel & van Ryzin, Minimum Earnings Regulation and the Stability of Marketplaces, SSRN 3502607 (version of August 24, 2022), Online Appendix p. 6 (PDF 34), proof of Theorem 3, second paragraph

import Mathlib
import Definitions.Def_MinEarnings_Static_Setting

namespace MinEarnings.Static

theorem static_of_wage_ge (D S : ℝ → ℝ) (M : ℝ) (hP : MinEarnings.Threshold.Primitives D S) (hM : 0 < M)
    (w z : ℕ → ℝ) (hfeas : MinEarnings.Threshold.IsFeasible w w) (heq : MinEarnings.Threshold.IsEquilibrium D S w w z)
    (hrule : MinEarnings.Threshold.MinEarningsRule D S M w w z) (t : ℕ)
    (hwt : M / MinEarnings.Threshold.util D S (w t) (z t) ≤ w t) :
    IsStaticallyStable D S M := by sorry

end MinEarnings.Static
