-- Prove2me | Theorems.Thm_MinEarnings_Static_static_implies_stable
-- name    : MinEarnings.Static.static_implies_stable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:40:29.431609+00:00
-- url     : https://prove2.me/theorems/c84e97a2-c521-4e47-a874-64e480b9ea28
-- title:
--   Proof of Theorem 3, Online Appendix p. 5 — a statically stable marketplace is (dynamically) stable
-- statement:
--   Let $D$ and $S$ satisfy the regularity assumptions and let $M>0$. If the $M$-minimum-earnings marketplace is statically stable, i.e. there are $p,w,z\ge 0$ and $u\in(0,1]$ solving
--   $$u=\frac{\min\{D(p),S(z)\}}{S(z)},\qquad z=w\,u,\qquad w\ge \frac{M}{u},\qquad p\ge w,$$
--   then the marketplace is stable: some feasible equilibrium-augmented policy obeying the minimum earnings rule $w_{t+1}\ge M/u(p_t,z_t)$ has bounded wages and non-negative profit in all but finitely many periods.
--
--   This is the easy direction of Theorem 3.
--
--   **Formalization Note** Stability includes the positivity pin $z_t>0$ of the equilibrium condition (see the definition file); a static solution meets it because $w \ge M/u > 0$.
-- source:
--   Asadpour, Lobel & van Ryzin, Minimum Earnings Regulation and the Stability of Marketplaces, SSRN 3502607 (version of August 24, 2022), Online Appendix p. 5 (PDF 33), proof of Theorem 3, first paragraph

import Mathlib
import Definitions.Def_MinEarnings_Static_Setting

namespace MinEarnings.Static

theorem static_implies_stable (D S : ℝ → ℝ) (M : ℝ) (hP : MinEarnings.Threshold.Primitives D S) (hM : 0 < M) :
    IsStaticallyStable D S M → MinEarnings.Threshold.IsStable D S M := by sorry

end MinEarnings.Static
